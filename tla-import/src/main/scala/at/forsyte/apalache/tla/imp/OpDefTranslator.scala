package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.{TlaOperDecl, TlaRecOperDecl}
import tla2sany.semantic.OpDefNode

/**
  * Translate an operator definition to a TlaOper.
  *
  * @author konnov
  */
class OpDefTranslator(context: Context) {
  def translate(node: OpDefNode): TlaOperDecl = {
    val params = node.getParams.toList map FormalParamTranslator().translate

    val nodeName = node.getName.toString.intern()
    if (!node.getInRecursive) {
      // non-recursive declarations are easy
      TlaOperDecl(nodeName, params,
        ExprOrOpArgNodeTranslator(context, OutsideRecursion()).translate(node.getBody))
    } else {
      // Introduce a dummy copy of the operator declaration.
//      val dummy = new TlaRecOperDecl(nodeName, params, NullEx)
      // Translate the body. The translator will translate the applications of
      // the dummy operator as applications of a formal parameter.
      val body = ExprOrOpArgNodeTranslator(context, InsideRecursion()).translate(node.getBody)
      // Finally, return the recursive operator declaration.
      new TlaRecOperDecl(nodeName, params, body)
    }
  }
}

object OpDefTranslator {
  def apply(context: Context): OpDefTranslator = {
    new OpDefTranslator(context)
  }
}
