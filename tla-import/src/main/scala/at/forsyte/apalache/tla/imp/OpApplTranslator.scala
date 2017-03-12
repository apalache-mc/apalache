package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import tla2sany.semantic.{ASTConstants, OpApplNode}

/**
  * Translate operator applications. As many TLA+ happen to be operators, this class will be complex...
  *
  * @author konnov
  */
class OpApplTranslator {
  def translate(node: OpApplNode): TlaEx = {
    if (node.getArgs.length == 0) {
      if (node.getOperator.getKind == ASTConstants.BuiltInKind) {
        // that must be a built-in constant operator
        translateBuiltinConst(node)
      } else {
        // this must be a reference to a constant (not a literal!), a variable, or another operator
        translateConstOper(node)
      }
    } else {
      if (node.getOperator.getKind == ASTConstants.BuiltInKind) {
        translateBuiltin(node)
      } else {
        throw new SanyImporterException("Unsupported operator type: " + node.getOperator)
      }
    }
  }

  // a built-in operator with zero arguments, that is, a built-in constant
  private def translateBuiltinConst(node: OpApplNode) = {
    // comparing the name seems to be the only way of learning about the actual operator
    node.getOperator.getName.toString match {
      case "FALSE"  => ValEx(TlaFalse) // here we disagree with tlatools and treat FALSE as a built-in value
      case "TRUE"   => ValEx(TlaTrue)  // ditto
      case _ => throw new SanyImporterException("Unsupported constant built-in operator: " + node.getOperator)
    }
  }

  // a constant operator, that is, a variable or a constant
  private def translateConstOper(node: OpApplNode) = {
    val oper = node.getOperator
    oper.getKind match {
      case ASTConstants.ConstantDeclKind =>
        NameEx(oper.getName.toString.intern())

      case ASTConstants.VariableDeclKind =>
        NameEx(oper.getName.toString.intern())
    }
  }

  // a non-constant built-in operator
  private def translateBuiltin(node: OpApplNode) = {
    OpApplTranslator.opcodeToIrOp.get(node.getOperator.getName.toString) match {
      case Some(op) =>
        val args = node.getArgs.toList.map { new ExprOrOpArgNodeTranslator().translate(_) }
        // if the arities do not match, there muts be a problem:
        // either in the definition of the IR operator, or in the map opcodeToIrOp
        assert(op.isCorrectArity(node.getArgs.length))
        OperEx(op, args: _*)

      case None =>
        throw new SanyImporterException("Unsupported operator: " + node.getOperator.getName)
    }
  }
}

object OpApplTranslator {
  /** a mapping from the Tlatools operators to our IR operators */
  val opcodeToIrOp: Map[String, TlaOper] = Map(
    ("=", TlaOper.eq),
    ("/=", TlaOper.ne),
    ("'", TlaActionOper.prime),
    ("\\lnot", TlaBoolOper.not),
    ("\\lor", TlaBoolOper.or),
    ("\\land", TlaBoolOper.and),
    ("\\equiv", TlaBoolOper.equiv),
    ("=>", TlaBoolOper.implies),
    ("SUBSET", TlaSetOper.subset),
    ("UNION", TlaSetOper.union),
    ("DOMAIN", TlaFunOper.domain),
    ("\\subseteq", TlaSetOper.subseteq),
    ("\\in", TlaSetOper.in),
    ("\\notin", TlaSetOper.notin),
    ("\\", TlaSetOper.setminus),
    ("\\intersect", TlaSetOper.cap),
    ("\\union", TlaSetOper.cup),
    ("$CartesianProd", TlaSetOper.times)
  )
}