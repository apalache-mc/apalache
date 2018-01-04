package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.TlaAssumeDecl
import tla2sany.semantic.AssumeNode

class AssumeTranslator(context: Context) {
  def translate(node: AssumeNode): TlaAssumeDecl = {
    val body = ExprOrOpArgNodeTranslator(context, OutsideRecursion())
      .translate(node.getAssume)
    TlaAssumeDecl(body)
  }
}

object AssumeTranslator {
  def apply(context: Context): AssumeTranslator = {
    new AssumeTranslator(context)
  }
}
