package at.forsyte.apalache.tla.typecheck.integration

import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaStr
import TypedPredefs._
import at.forsyte.apalache.tla.typecheck.ModelValueHandler

/**
 * This class uses the map of types to set the types of TLA+ expressions and declarations.
 *
 * @param types a map from unique identifiers to types
 */
class TypeRewriter(tracker: TransformationTracker, defaultTag: UID => TypeTag)(types: Map[UID, TlaType1]) {
  def apply(e: TlaEx): TlaEx = {
    def transform: TlaEx => TlaEx = tracker.trackEx {
      case ValEx(value @ TlaStr(s)) =>
        // A record constructor uses strings to represent the field names,
        // which are not propagated to the type checker. Hence, we bypass a query to the types map.
        ValEx(value)(Typed(ModelValueHandler.modelValueOrString(s)))

      case ex @ ValEx(value) =>
        ValEx(value)(getOrDefault(ex.ID))

      case ex @ NameEx(name) =>
        NameEx(name)(getOrDefault(ex.ID))

      case ex @ OperEx(TlaFunOper.except, fun, args @ _*) =>
        // [f EXCEPT ![e1] = e2, ![e3] = e4, ...]
        // We provide special treatment for this expression, as indices are always wrapped in a tuple.
        // Alternatively, we could add this complexity to the translator `ToEtcExpr`.
        // However, the code in `ToEtcExpr` is hard for understanding already.
        val taggedFun = transform(fun)

        def wrapIndexWithTuple: TlaEx => TlaEx = tracker.trackEx {
          case OperEx(TlaFunOper.tuple, indices @ _*) =>
            val taggedIndices = indices map transform
            val typesOfIndices = taggedIndices.map(_.typeTag.asTlaType1())
            val tupleTag = Typed(TupT1(typesOfIndices: _*))
            OperEx(TlaFunOper.tuple, taggedIndices: _*)(tupleTag)

          case e =>
            throw new IllegalArgumentException(s"Expected a tuple as an index in EXCEPT, found: $e")
        }

        val (accessors, newValues) = TlaOper.deinterleave(args)
        val transformedAccessors = accessors map wrapIndexWithTuple
        val transformedValues = newValues map transform
        val transformedArgs = TlaOper.interleave(transformedAccessors, transformedValues)

        OperEx(TlaFunOper.except, taggedFun +: transformedArgs: _*)(getOrDefault(ex.ID))

      case ex @ OperEx(oper, args @ _*) =>
        val newArgs = args.map(this(_))
        OperEx(oper, newArgs: _*)(getOrDefault(ex.ID))

      case ex @ LetInEx(body, defs @ _*) =>
        LetInEx(this(body), defs.map(applyToOperDecl): _*)(getOrDefault(ex.ID))
    }

    transform(e)
  }

  def apply(decl: TlaDecl): TlaDecl = {
    def transform: TlaDecl => TlaDecl = tracker.trackDecl {
      case d @ TlaConstDecl(_) =>
        decl.withTag(getOrDefault(d.ID))

      case d @ TlaVarDecl(_) =>
        decl.withTag(getOrDefault(d.ID))

      case d @ TlaAssumeDecl(body) =>
        TlaAssumeDecl(this(body))(getOrDefault(d.ID))

      case d @ TlaTheoremDecl(name, body) =>
        TlaTheoremDecl(name, this(body))(getOrDefault(d.ID))

      case opdef @ TlaOperDecl(_, _, _) =>
        applyToOperDecl(opdef)
    }

    transform(decl)
  }

  private def applyToOperDecl(decl: TlaOperDecl): TlaOperDecl =
    decl.copy(body = this(decl.body))(getOrDefault(decl.ID))

  private def getOrDefault(uid: UID): TypeTag = {
    types.get(uid) match {
      case Some(tt) => Typed(tt)
      case None     => defaultTag(uid)
    }
  }
}
