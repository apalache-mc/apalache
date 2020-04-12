package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import tla2sany.semantic.{OpApplNode, OpDefNode}

/**
  * Translate an operator definition to a TlaOper.
  *
  * @author konnov
  */
class OpDefTranslator(sourceStore: SourceStore, context: Context) {
  def translate(node: OpDefNode): TlaOperDecl = {
    val params = node.getParams.toList map FormalParamTranslator().translate
    val nodeName = node.getName.toString.intern()

    if (!node.getInRecursive) {
      node.getBody match {
        case app: OpApplNode if "$RecursiveFcnSpec" == app.getOperator.getName.toString =>
          // this is a definition of a recursive function, translate to recFunDef
          val body = ExprOrOpArgNodeTranslator(sourceStore, context, OutsideRecursion())
            .translate(node.getBody)
          // the body still can refer to the function by its name, replace it with recFunRef
          val replaced = ReplaceFixed(NameEx(nodeName), OperEx(TlaFunOper.recFunRef), new IdleTracker())(body)
          // store the source location
          sourceStore.addRec(replaced, SourceLocation(node.getBody.getLocation))
          // return the operator whose body is a recursive function
          val operDecl = TlaOperDecl(nodeName, List(), replaced)
          operDecl.isRecursive = false
          operDecl

        case _ =>
          // non-recursive declarations are easy
          TlaOperDecl(nodeName, params,
            ExprOrOpArgNodeTranslator(sourceStore, context, OutsideRecursion())
              .translate(node.getBody))
      }
    } else {
      // in recursive declarations, the applications of recursive operators are replaced by calls to formal parameters
      val body = ExprOrOpArgNodeTranslator(sourceStore, context, InsideRecursion())
        .translate(node.getBody)
      val decl = TlaOperDecl(nodeName, params, body)
      decl.isRecursive = true
      decl
    }
  }
}

object OpDefTranslator {
  def apply( sourceStore: SourceStore, context: Context) : OpDefTranslator = {
    new OpDefTranslator(sourceStore, context)
  }
}
