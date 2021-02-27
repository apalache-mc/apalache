package at.forsyte.apalache.tla.typecheck.integration

import at.forsyte.apalache.tla.lir.transformations.TransformationTracker
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.typecheck.{StrT1, TlaType1, TypingException}

/**
 * This class uses the map of types to set the types of TLA+ expressions and declarations.
 *
 * @param types a map from unique identifiers to types
 */
class TypeRewriter(tracker: TransformationTracker)(types: Map[UID, TlaType1]) {
  def apply(e: TlaEx): TlaEx = {
    def transform: TlaEx => TlaEx = tracker.trackEx {
      case ex @ OperEx(oper, args @ _*) =>
        val newArgs = args.map(this(_))
        OperEx(oper, newArgs: _*)(Typed(getOrThrow(ex.ID)))

      case ex @ LetInEx(body, defs @ _*) =>
        LetInEx(this(body), defs.map(applyToOperDecl): _*)(getOrThrow(ex.ID))

      case ValEx(value @ TlaStr(_)) =>
        // A record constructor uses strings to represent the field names,
        // which are not propagated to the type checker. Hence, we bypass a query to the types map.
        ValEx(value)(Typed(StrT1()))

      case ex @ ValEx(value) =>
        ValEx(value)(getOrThrow(ex.ID))

      case ex @ NameEx(name) =>
        NameEx(name)(getOrThrow(ex.ID))
    }

    transform(e)
  }

  def apply(decl: TlaDecl): TlaDecl = {
    def transform: TlaDecl => TlaDecl = tracker.trackDecl {
      case TlaConstDecl(_) | TlaVarDecl(_) =>
        decl.withType(getOrThrow(decl.ID))

      case TlaAssumeDecl(body) =>
        TlaAssumeDecl(this(body))(getOrThrow(decl.ID))

      case TlaTheoremDecl(name, body) =>
        TlaTheoremDecl(name, this(body))(getOrThrow(decl.ID))

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
