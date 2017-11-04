package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Integer comparisons: <, <=, >, >=. For equality and inequality, check EqRule.
  *
  * @author Igor Konnov
  */
class IntCmpRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.lt, _, _)
           | OperEx(TlaArithOper.le, _, _)
           | OperEx(TlaArithOper.gt, _, _)
           | OperEx(TlaArithOper.ge, _, _)
      => true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(oper: TlaArithOper, lex @ NameEx(left), rex @ NameEx(right))
      if (oper == TlaArithOper.lt || oper == TlaArithOper.le
        || oper == TlaArithOper.gt || oper == TlaArithOper.ge)
    =>
      val leftState = rewriter.coerce(state.setRex(lex), IntTheory())
      val rightState = rewriter.coerce(leftState.setRex(rex), IntTheory())
      // compare integers directly in SMT
      val eqPred = state.solverCtx.introBoolConst()
      val cons =
        OperEx(TlaOper.eq,
          NameEx(eqPred),
          OperEx(oper, leftState.ex, rightState.ex))
      state.solverCtx.assertGroundExpr(cons)
      val finalState = state.setTheory(BoolTheory()).setRex(NameEx(eqPred))
      rewriter.coerce(finalState, state.theory)

    case _ =>
      throw new RewriterException("IntCmpRule is not applicable")
  }
}
