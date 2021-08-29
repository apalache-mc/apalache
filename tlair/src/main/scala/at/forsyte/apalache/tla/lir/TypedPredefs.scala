package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.values._

object TypedPredefs {
  type Tag = Typed[TlaType1]

  /**
   * An implicit conversion of an expression to a builder block.
   *
   * @param ex a TLA+ expression
   * @return a builder block
   */
  implicit def tlaExToBlock(ex: TlaEx): BuilderTlaExWrapper = {
    BuilderTlaExWrapper(ex)
  }

  /**
   * An implicit conversion of an expression to a typed builder expression.
   * We need this implicit conversion in addition to tlaExToBlock, as Scala looks only for one implicit conversion,
   * whereas we need two in this case.
   *
   * @param ex a TLA+ expression
   * @return a typed builder block
   */
  implicit def tlaExToBuilderExAsTyped(ex: TlaEx): BuilderExAsTyped = {
    BuilderExAsTyped(BuilderTlaExWrapper(ex))
  }

  /**
   * An implicit conversion of a sequence of expressions to a sequence of builder blocks.
   *
   * @param es a sequence of TLA+ expressions
   * @return the corresponding sequence of builder blocks
   */
  implicit def seqOfTlaExToSeqOfBlocks(es: Seq[TlaEx]): Seq[BuilderTlaExWrapper] = {
    es.map(BuilderTlaExWrapper)
  }

  /**
   * An implicit wrapper around TypeTag that extract the type out of Typed(_: TlaType1).
   *
   * TODO: shall we remove this implicit conversion in favor of TlaType1.fromTypeTag?
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
    def as(topType: TlaType1): TlaDecl = {
      buildTyped(Map.empty, topType)
    }

    // TODO: Remove it, as soon as we migrate to the version that does not use string aliases
    def typed(types: Map[String, TlaType1], alias: String): TlaDecl = {
      types.get(alias) match {
        case Some(tt) => buildTyped(types, tt)
        case None     => throw new BuilderError(s"No type for alias $alias")
      }
    }

    private def buildTyped(types: Map[String, TlaType1], topType: TlaType1): TlaDecl = {
      block match {
        case BuilderOperDecl(name, formalParams, body) =>
          val typedBody = new BuilderExAsTyped(body).buildTyped(types, None)
          TlaOperDecl(name, formalParams, typedBody)(Typed(topType))
      }
    }
  }

  implicit class BuilderOperDeclAsTyped(block: BuilderOperDecl) {
    def as(topType: TlaType1): TlaOperDecl = {
      BuilderDeclAsTyped(block).as(topType).asInstanceOf[TlaOperDecl]
    }

    def typedOperDecl(types: Map[String, TlaType1], alias: String): TlaOperDecl = {
      BuilderDeclAsTyped(block).typed(types, alias).asInstanceOf[TlaOperDecl]
    }
  }

  implicit class BuilderExAsTyped(block: BuilderEx) {
    def typed(): TlaEx = {
      buildTyped(Map.empty, None)
    }

    /**
     * A shortcut for typed(topType)
     *
     * @param topType the type to use for the top expression
     * @return an expression with the given type
     */
    def as(topType: TlaType1): TlaEx = {
      typed(topType)
    }

    def typed(topType: TlaType1): TlaEx = {
      buildTyped(Map.empty, Some(topType))
    }

    // TODO: Remove it, as soon as we migrate to the version that does not use string aliases
    def typed(types: Map[String, TlaType1], alias: String): TlaEx = {
      val typeFromAlias = findTypeOrThrow(types, alias)
      buildTyped(types, Some(typeFromAlias))
    }

    // Build a typed expression. For the backward-compatibility, we accept the map of type aliases.
    // This map will be removed in the future.
    def buildTyped(types: Map[String, TlaType1], topType: Option[TlaType1]): TlaEx = {
      block match {
        case BuilderTlaExWrapper(ex) =>
          topType.map(tt => ex.withTag(Typed(tt))).getOrElse(ex)

        case BuilderName(name) =>
          topType match {
            case Some(tt) =>
              NameEx(name)(Typed(tt))

            case None =>
              throw new BuilderError(s"Missing type annotation in: name $name")
          }

        case BuilderAlias(target, alias) =>
          val typeFromAlias = findTypeOrThrow(types, alias)
          BuilderExAsTyped(target).buildTyped(types, Some(typeFromAlias))

        case BuilderOper(oper, args @ _*) =>
          topType match {
            case Some(tt) =>
              val builtArgs = args map (a => BuilderExAsTyped(a).buildTyped(types, None))
              OperEx(oper, builtArgs: _*)(Typed(tt))

            case None =>
              throw new BuilderError(s"Missing type annotation in: operator ${oper.name}")
          }

        case BuilderLet(body, defs @ _*) =>
          val builtBody = BuilderExAsTyped(body).buildTyped(types, None)
          LetInEx(builtBody, defs: _*)(builtBody.typeTag)

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

    private def findTypeOrThrow(types: Map[String, TlaType1], alias: String): TlaType1 = {
      if (alias == "?") {
        throw new BuilderError(s"""An expression is missing a type alias, use tla.foo(...) ? "alias" """)
      } else {
        types.get(alias) match {
          case Some(tt) => tt
          case None     => throw new BuilderError(s"No type given for the type alias $alias")
        }
      }
    }
  }
}
