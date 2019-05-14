package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.imp.src.{SourceLocation, SourceStore}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import tla2sany.semantic.{OpApplNode, OpDefNode}

/**
  * Translate an operator definition to a TlaOper.
  *
  * @author konnov
  */
class OpDefTranslator(environmentHandler: EnvironmentHandler, sourceStore: SourceStore, context: Context) {
  def translate(node: OpDefNode): TlaOperDecl = {
    val params = node.getParams.toList map FormalParamTranslator().translate
    val nodeName = node.getName.toString.intern()

    if (!node.getInRecursive) {
      node.getBody match {
        case app: OpApplNode if "$RecursiveFcnSpec" == app.getOperator.getName.toString =>
          // this is a definition of a recursive function
          val body = ExprOrOpArgNodeTranslator(environmentHandler, sourceStore, context, OutsideRecursion())
            .translate(node.getBody)
          // declare a nullary recursive operator instead of a recursive function
          val newBody = replaceFunWithOper(nodeName, body)
          // store the source location
          sourceStore.addRec(environmentHandler.identify(newBody), SourceLocation(node.getBody.getLocation))
          // return the operator whose body is a recursive function
          val operDecl = TlaOperDecl(nodeName, List(), newBody)
          operDecl.isRecursive = true
          operDecl

        case _ =>
          // non-recursive declarations are easy
          TlaOperDecl(nodeName, params,
            ExprOrOpArgNodeTranslator(environmentHandler, sourceStore, context, OutsideRecursion())
              .translate(node.getBody))
      }
    } else {
      // in recursive declarations, the applications of recursive operators are replaced by calls to formal parameters
      val body = ExprOrOpArgNodeTranslator(environmentHandler, sourceStore, context, InsideRecursion())
        .translate(node.getBody)
      val decl = TlaOperDecl(nodeName, params, body)
      decl.isRecursive = true
      decl
    }
  }

  private def replaceFunWithOper(name: String, body: TlaEx): TlaEx = {
    def replace(e: TlaEx): TlaEx = e match {
      case NameEx(n) if n == name =>
        environmentHandler.identify(OperEx(TlaOper.apply, NameEx(n)))

      case OperEx(o, args@_*) =>
        environmentHandler.identify(OperEx(o, args map replace: _*))

      case _ => e
    }

    replace(body)
  }
}

object OpDefTranslator {
  def apply(environmentHandler: EnvironmentHandler, sourceStore: SourceStore, context: Context): OpDefTranslator = {
    new OpDefTranslator(environmentHandler, sourceStore, context)
  }
}
