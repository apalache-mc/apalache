package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.TlaAssumeDecl
import tla2sany.semantic.AssumeNode

class AssumeTranslator(sourceStore: SourceStore, annotationStore: TlaAnnotationStore, context: Context) {
  def translate(node: AssumeNode): TlaAssumeDecl = {
    val body =
      ExprOrOpArgNodeTranslator(sourceStore, annotationStore, context, OutsideRecursion())
        .translate(node.getAssume)
    TlaAssumeDecl(body)
  }
}

object AssumeTranslator {
  def apply(ls: SourceStore, as: TlaAnnotationStore, ctx: Context): AssumeTranslator = {
    new AssumeTranslator(ls, as, ctx)
  }
}
