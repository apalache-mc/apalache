package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import tla2sany.semantic.{OpApplNode, OpDefNode}

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
      node.getBody match {
        case app: OpApplNode if "$RecursiveFcnSpec" == app.getOperator.getName.toString =>
          // this is a definition of a recursive function
          val body = ExprOrOpArgNodeTranslator(context, OutsideRecursion()).translate(node.getBody)
          // declare a nullary recursive operator instead of a recursive function
          val newBody = replaceFunWithOper(nodeName, body)
          new TlaRecOperDecl(nodeName, List(), newBody)

        case _ =>
          // non-recursive declarations are easy
          TlaOperDecl(nodeName, params,
            ExprOrOpArgNodeTranslator(context, OutsideRecursion()).translate(node.getBody))
      }
    } else {
      // in recursive declarations, the applications of recursive operators are replaced by calls to formal parameters
      val body = ExprOrOpArgNodeTranslator(context, InsideRecursion()).translate(node.getBody)
      new TlaRecOperDecl(nodeName, params, body)
    }
  }

  private def replaceFunWithOper(name: String, body: TlaEx): TlaEx = {
    def replace(e: TlaEx): TlaEx = e match {
      case NameEx(n) if n == name =>
        OperEx(TlaOper.apply, NameEx(n))

      case OperEx(o, args@_*) =>
        OperEx(o, args map replace: _*)

      case _ => e
    }

    replace(body)
  }
}

object OpDefTranslator {
  def apply(context: Context): OpDefTranslator = {
    new OpDefTranslator(context)
  }
}
