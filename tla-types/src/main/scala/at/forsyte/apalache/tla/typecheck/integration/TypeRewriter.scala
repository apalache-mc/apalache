package at.forsyte.apalache.tla.typecheck.integration

import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecheck.{StrT1, TlaType1, TupT1, TypingException}

/**
 * This class uses the map of types to set the types of TLA+ expressions and declarations.
 *
 * @param types a map from unique identifiers to types
 */
class TypeRewriter(tracker: TransformationTracker)(types: Map[UID, TlaType1]) {
  def apply(e: TlaEx): TlaEx = {
    def transform: TlaEx => TlaEx = tracker.trackEx {
      case ValEx(value @ TlaStr(_)) =>
        // A record constructor uses strings to represent the field names,
        // which are not propagated to the type checker. Hence, we bypass a query to the types map.
        ValEx(value)(Typed(StrT1()))

      case ex @ ValEx(value) =>
        ValEx(value)(getOrThrow(ex.ID))

      case ex @ NameEx(name) =>
        NameEx(name)(getOrThrow(ex.ID))

      case ex @ OperEx(TlaFunOper.except, fun, args @ _*) =>
        // [f EXCEPT ![e1] = e2, ![e3] = e4, ...]
        // We provide a special treatment for this expression, as a single-argument index is always wrapped in a tuple.
        // Alternatively, we could add this complexity to the translator `ToEtcExpr`.
        // However, the code in `ToEtcExpr` is hard for understanding already.
        val taggedFun = transform(fun)

        def transformIndex: TlaEx => TlaEx = tracker.trackEx {
          case OperEx(TlaFunOper.tuple, singleIndex) =>
            val indexType = getOrThrow(singleIndex.ID)
            val taggedIndex = transformIndex(singleIndex)
            // The crux of having the special treatment for except:
            // Wrap the single index with a tuple and tag the accessor with the tuple type.
            OperEx(TlaFunOper.tuple, taggedIndex)(Typed(TupT1(indexType.myType)))

          case multiIndexTuple =>
            transform(multiIndexTuple)
        }

        val accessorsWithTaggedValues =
          args
            .grouped(2)
            .flatMap {
              case Seq(a, b) => Seq(transformIndex(a), transform(b))
              case orphan    => throw new TypingException(s"Orphan ${orphan} in except expression: ${ex}")
            }
            .toList

        OperEx(TlaFunOper.except, taggedFun +: accessorsWithTaggedValues: _*)(getOrThrow(ex.ID))

      case ex @ OperEx(oper, args @ _*) =>
        val newArgs = args.map(this(_))
        OperEx(oper, newArgs: _*)(Typed(getOrThrow(ex.ID)))

      case ex @ LetInEx(body, defs @ _*) =>
        LetInEx(this(body), defs.map(applyToOperDecl): _*)(getOrThrow(ex.ID))
    }

    transform(e)
  }

  def apply(decl: TlaDecl): TlaDecl = {
    def transform: TlaDecl => TlaDecl = tracker.trackDecl {
      case d @ TlaConstDecl(_) =>
        decl.withType(getOrThrow(d.ID))

      case d @ TlaVarDecl(_) =>
        decl.withType(getOrThrow(d.ID))

      case d @ TlaAssumeDecl(body) =>
        TlaAssumeDecl(this(body))(getOrThrow(d.ID))

      case d @ TlaTheoremDecl(name, body) =>
        TlaTheoremDecl(name, this(body))(getOrThrow(d.ID))

      case opdef @ TlaOperDecl(_, _, _) =>
        applyToOperDecl(opdef)
    }

    transform(decl)
  }

  private def applyToOperDecl(decl: TlaOperDecl): TlaOperDecl = {
    TlaOperDecl(decl.name, decl.formalParams, this(decl.body))(getOrThrow(decl.ID))
  }

  private def getOrThrow(uid: UID): Typed[TlaType1] = {
    types.get(uid) match {
      case Some(tt) => Typed(tt)
      case None     => throw new TypingException("No type for uid: " + uid)
    }
  }
}
