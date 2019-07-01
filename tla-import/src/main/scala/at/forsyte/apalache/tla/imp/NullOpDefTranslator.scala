package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import tla2sany.semantic.{OpApplNode, OpDefNode}

/**
  * DummyOpDefTranslator creates a proper operator declaration but produces NullEx instead of the body.
  *
  * @author konnov
  */
class NullOpDefTranslator(sourceStore: SourceStore, context: Context) {
  def translate(node: OpDefNode): TlaOperDecl = {
    val params = node.getParams.toList map FormalParamTranslator().translate
    val nodeName = node.getName.toString.intern()
    TlaOperDecl(nodeName, params, NullEx)
  }
}

object NullOpDefTranslator {
  def apply(sourceStore: SourceStore, context: Context): NullOpDefTranslator = {
    new NullOpDefTranslator(sourceStore, context)
  }
}

