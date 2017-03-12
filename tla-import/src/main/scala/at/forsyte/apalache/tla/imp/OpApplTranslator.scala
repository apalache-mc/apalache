package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaInt}
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import tla2sany.semantic.{ASTConstants, OpApplNode}

/**
  * Translate operator applications. As many TLA+ happen to be operators, this class will be complex...
  *
  * @author konnov
  */
class OpApplTranslator {
  def translate(node: OpApplNode): TlaEx = {
    // TODO: extend to the non-constant operators in the future
    assert(node.getArgs.length == 0)

    if (node.getOperator.getKind == ASTConstants.BuiltInKind && node.getArgs.length == 0) {
      // that must be a built-in constant operator
      translateConstBuiltin(node)
    } else {
      throw new SanyImporterException("Unsupported operator type: " + node.getOperator)
    }
  }

  private def translateConstBuiltin(node: OpApplNode) = {
    // comparing the name seems to be the only way of learning about the actual operator
    node.getOperator.getName.toString match {
      case "FALSE"  => ValEx(TlaBool(false)) // here we disagree with tlatools and treat FALSE as a built-in TLA+ value
      case "TRUE"   => ValEx(TlaBool(true))  // ditto
      case _ => throw new SanyImporterException("Unsupported constant built-in operator: " + node.getOperator)
    }
  }
}
