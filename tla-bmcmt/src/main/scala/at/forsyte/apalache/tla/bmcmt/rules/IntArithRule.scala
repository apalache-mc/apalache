package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Integer arithmetic operations: +, -, *, div, mod.
  * Implements rule SE-INT-ARITH1.
  *
  * @author Igor Konnov
  */
class IntArithRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.plus, _, _)
           | OperEx(TlaArithOper.minus, _, _)
           | OperEx(TlaArithOper.mult, _, _)
           | OperEx(TlaArithOper.div, _, _)
           | OperEx(TlaArithOper.mod, _, _)
      => true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(oper: TlaArithOper, lex @ NameEx(left), rex @ NameEx(right))
      if (oper == TlaArithOper.plus || oper == TlaArithOper.minus
        || oper == TlaArithOper.mult || oper == TlaArithOper.div || oper == TlaArithOper.mod)
    =>
      val leftState = rewriter.coerce(state.setRex(lex), IntTheory())
      val rightState = rewriter.coerce(leftState.setRex(rex), IntTheory())
      // introduce an integer constant to store the result
      val intConst = state.solverCtx.introIntConst()
      val cons =
        OperEx(TlaOper.eq,
          NameEx(intConst),
          OperEx(oper, leftState.ex, rightState.ex))
      state.solverCtx.assertGroundExpr(cons)
      val finalState = state.setTheory(IntTheory()).setRex(NameEx(intConst))
      rewriter.coerce(finalState, state.theory)

    case _ =>
      throw new RewriterException("IntArithRule is not applicable")
  }
}
