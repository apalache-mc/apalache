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
    val params = node.getParams.toList map FormalParamTranslator().translate

    TlaOperDecl(node.getName.toString.intern(), params,
      ExprOrOpArgNodeTranslator(context).translate(node.getBody))
  }
}

object OpDefTranslator {
  def apply(context: Context): OpDefTranslator = {
    new OpDefTranslator(context)
  }
}
