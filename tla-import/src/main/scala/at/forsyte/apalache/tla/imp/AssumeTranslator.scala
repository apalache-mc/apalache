package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaAssumeDecl
import tla2sany.semantic.AssumeNode

class AssumeTranslator(sourceStore: SourceStore, context: Context) {
  def translate(node: AssumeNode): TlaAssumeDecl = {
    val body =
      ExprOrOpArgNodeTranslator(sourceStore, context, OutsideRecursion())
        .translate(node.getAssume)
    TlaAssumeDecl(body)
  }
}

object AssumeTranslator {
  def apply(ls: SourceStore, ctx: Context): AssumeTranslator = {
    new AssumeTranslator(ls, ctx)
  }
}
