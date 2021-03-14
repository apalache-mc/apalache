package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir._

object TypedPredefs {
  type Tag = Typed[TlaType1]

  /**
   * An implicit conversion of an expression to a builder block
   *
   * @param ex a TLA+ expression
   * @return a builder block
   */
  implicit def tlaExToBlock(ex: TlaEx): BuilderTlaExWrapper = {
    BuilderTlaExWrapper(ex)
  }

  /**
   * An implicit conversion of a sequence of expressions to a sequence of builder blocks.
   *
   * @param es a sequence of TLA+ expressions
   * @return the corresponding sequence of builder blocks
   */
  implicit def seqOfTlaExToSeqOfBlocks(es: Seq[TlaEx]): Seq[BuilderTlaExWrapper] = {
    es.map(tlaExToBlock)
  }

  /**
   * An implicit wrapper around TypeTag that extract the type out of Typed(_: TlaType1).
   *
   * @param tag a type tag
   */
  implicit class TypeTagAsTlaType1(tag: TypeTag) {

    /**
     * Unwrap a type tag of the form Typed(_: TlaType1) into TlaType1. If the tag does not match this pattern,
     * throw TypingException.
     *
     * @return the type that is stored in the tag
     */
    def asTlaType1(): TlaType1 = {
      tag match {
        case Typed(tt: TlaType1) => tt

        case _ =>
          throw new TypingException("Expected Typed(_: TlaType1), found: " + tag)
      }
    }
  }

  implicit class BuilderDeclAsTyped(block: BuilderDecl) {
    def typed(topType: TlaType1): TlaDecl = {
      typed(Map("t" -> topType), "t")
    }

    def typed(types: Map[String, TlaType1], alias: String): TlaDecl = {
      block match {
        case BuilderOperDecl(name, formalParams, body) =>
          val typedBody = new BuilderExAsTyped(body).typed(types, "?")
          types.get(alias) match {
            case Some(tt) => TlaOperDecl(name, formalParams, typedBody)(Typed(tt))
            case None     => throw new BuilderError(s"No type for alias $alias")
          }
      }
    }
  }

  implicit class BuilderOperDeclAsTyped(block: BuilderOperDecl) {
    def typedOperDecl(topType: TlaType1): TlaOperDecl = {
      BuilderDeclAsTyped(block).typed(topType).asInstanceOf[TlaOperDecl]
    }
  }

  implicit class BuilderExAsTyped(block: BuilderEx) {
    def typed(): TlaEx = {
      typed(Map.empty, "?")
    }

    def typed(topType: TlaType1): TlaEx = {
      typed(Map("t" -> topType), "t")
    }

    def typed(types: Map[String, TlaType1], alias: String): TlaEx = {
      block match {
        case BuilderTlaExWrapper(ex) =>
          ex

        case BuilderName(name) =>
          types.get(alias) match {
            case Some(tt) => NameEx(name)(Typed(tt))
            case None     => throw new BuilderError(s"No type for alias $alias")
          }

        case BuilderAlias(target, newAlias) =>
          target.typed(types, newAlias)

        case BuilderOper(oper, args @ _*) =>
          val builtArgs = args map (a => a.typed(types, "?"))
          types.get(alias) match {
            case Some(tt) => OperEx(oper, builtArgs: _*)(Typed(tt))
            case None     => throw new BuilderError(s"No type for alias $alias")
          }

        case BuilderLet(body, defs @ _*) =>
          val builtBody = body.typed(types, "?")
          types.get(alias) match {
            case Some(tt) => LetInEx(builtBody, defs: _*)(Typed(tt))
            case None     => throw new BuilderError(s"No type for alias $alias")
          }

        case BuilderVal(TlaInt(value)) =>
          ValEx(TlaInt(value))(Typed(IntT1()))

        case BuilderVal(TlaBool(value)) =>
          ValEx(TlaBool(value))(Typed(BoolT1()))

        case BuilderVal(TlaStr(value)) =>
          ValEx(TlaStr(value))(Typed(StrT1()))

        case BuilderVal(TlaIntSet) =>
          ValEx(TlaIntSet)(Typed(SetT1(IntT1())))

        case BuilderVal(TlaNatSet) =>
          ValEx(TlaNatSet)(Typed(SetT1(IntT1())))

        case BuilderVal(TlaBoolSet) =>
          ValEx(TlaBoolSet)(Typed(SetT1(BoolT1())))

        case BuilderVal(TlaRealSet) =>
          ValEx(TlaRealSet)(Typed(SetT1(RealT1())))

        case BuilderVal(v) =>
          throw new BuilderError("Unexpected value: " + v)
      }
    }
  }

}
