package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir._
import tla2sany.semantic.OpDefNode

/**
 * DummyOpDefTranslator creates a proper operator declaration but produces NullEx instead of the body.
 *
 * @author
 *   konnov
 */
class NullOpDefTranslator {
  def translate(node: OpDefNode): TlaOperDecl = {
    val params = node.getParams.toList.map(FormalParamTranslator().translate)
    val nodeName = node.getName.toString.intern()
    TlaOperDecl(nodeName, params, NullEx)(Untyped)
  }
}

object NullOpDefTranslator {
  def apply(): NullOpDefTranslator = {
    new NullOpDefTranslator
  }
}
