package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.store.AnnotationStore
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{TlaAssumeDecl, Untyped}
import tla2sany.semantic.AssumeNode

class AssumeTranslator(
    sourceStore: SourceStore, annotationStore: AnnotationStore, context: Context
) {
  def translate(node: AssumeNode): TlaAssumeDecl = {
    val body =
      ExprOrOpArgNodeTranslator(
          sourceStore,
          annotationStore,
          context,
          OutsideRecursion()
      ).translate(node.getAssume)
    TlaAssumeDecl(body)(Untyped())
  }
}

object AssumeTranslator {
  def apply(
      ls: SourceStore, as: AnnotationStore, ctx: Context
  ): AssumeTranslator = {
    new AssumeTranslator(ls, as, ctx)
  }
}
