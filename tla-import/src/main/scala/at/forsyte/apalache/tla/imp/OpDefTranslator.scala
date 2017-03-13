package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaOperDecl, ValEx}
import at.forsyte.apalache.tla.lir.values.TlaInt
import tla2sany.semantic.OpDefNode

/**
  * Translate an operator to a TlaOper.
  *
  * @author konnov
  */
class OpDefTranslator(context: Context) {
  def translate(node: OpDefNode): TlaOperDecl = {
    TlaOperDecl(node.getName.toString, List(), new ExprOrOpArgNodeTranslator(context).translate(node.getBody))
  }
}
