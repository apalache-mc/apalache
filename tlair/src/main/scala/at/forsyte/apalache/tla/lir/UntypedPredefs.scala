package at.forsyte.apalache.tla.lir

/**
 * Default settings for the untyped language layer. To use the `Untyped()` tag, import the definitions from `UntypedPredefs`.
 */
object UntypedPredefs {
  implicit val untyped: TypeTag = Untyped()

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

  implicit def builderExToTlaEx(block: BuilderEx): TlaEx = {
    block match {
      case BuilderTlaExWrapper(ex) =>
        ex

      case BuilderName(name) =>
        NameEx(name)(Untyped())

      case BuilderAlias(target, _) =>
        builderExToTlaEx(target)

      case BuilderOper(oper, args @ _*) =>
        val builtArgs = args map (a => builderExToTlaEx(a))
        OperEx(oper, builtArgs: _*)

      case BuilderLet(body, defs @ _*) =>
        val builtBody = builderExToTlaEx(body)
        LetInEx(builtBody, defs: _*)

      case BuilderVal(value) =>
        ValEx(value)(Untyped())
    }
  }

  implicit def builderDeclToTlaDecl(block: BuilderDecl): TlaDecl = {
    block match {
      case BuilderOperDecl(name, formalParams, body) =>
        TlaOperDecl(name, formalParams, body)(Untyped())

      case _ =>
        throw new BuilderError("Unexpected case of BuilderDecl: " + block)
    }
  }

  implicit class BuilderExAsUntyped(block: BuilderEx) {
    def untyped(): TlaEx = {
      builderExToTlaEx(block)
    }
  }

  implicit class BuilderDeclAsUntyped(block: BuilderDecl) {
    def untyped(): TlaDecl = {
      builderDeclToTlaDecl(block)
    }
  }

  implicit class BuilderOperDeclAsUntyped(block: BuilderOperDecl) {
    def untypedOperDecl(): TlaOperDecl = {
      TlaOperDecl(block.name, block.formalParams, block.body)(Untyped())
    }
  }

}
