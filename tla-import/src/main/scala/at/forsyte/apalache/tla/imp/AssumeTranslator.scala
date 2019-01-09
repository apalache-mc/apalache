package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{EnvironmentHandler, TlaAssumeDecl}
import tla2sany.semantic.AssumeNode

class AssumeTranslator(environmentHandler: EnvironmentHandler, sourceStore: SourceStore, context: Context) {
  def translate(node: AssumeNode): TlaAssumeDecl = {
    val body = ExprOrOpArgNodeTranslator(environmentHandler, sourceStore, context, OutsideRecursion())
      .translate(node.getAssume)
    TlaAssumeDecl(body)
  }
}

object AssumeTranslator {
  def apply(eh: EnvironmentHandler, ls: SourceStore, ctx: Context): AssumeTranslator = {
    new AssumeTranslator(eh, ls, ctx)
  }
}
