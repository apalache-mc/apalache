package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaOperDecl, ValEx}
import at.forsyte.apalache.tla.lir.values.TlaInt
import tla2sany.semantic.OpDefNode

/**
  * Translate an operator to a TlaOper.
  *
  * @author konnov
  */
class OpDefTranslator {
  def translate(node: OpDefNode): TlaOperDecl = {
    TlaOperDecl(node.getName.toString, List(), new ExprNodeTranslator().translate(node.getBody))
  }
}
