package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Integer comparisons: <, <=, >, >=. For equality and inequality, check EqRule and NeqRule.
  * Implements SE-INT-CMP1.
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
    case OperEx(oper: TlaArithOper, left, right)
      if (oper == TlaArithOper.lt || oper == TlaArithOper.le
        || oper == TlaArithOper.gt || oper == TlaArithOper.ge)
    =>
      val leftState = rewriter.rewriteUntilDone(state.setTheory(IntTheory()).setRex(left))
      val rightState = rewriter.rewriteUntilDone(state.setTheory(IntTheory()).setRex(right))
      // compare integers directly in SMT
      val eqPred = rewriter.solverContext.introBoolConst()
      val cons =
        OperEx(TlaOper.eq,
          NameEx(eqPred),
          OperEx(oper, leftState.ex, rightState.ex))
      rewriter.solverContext.assertGroundExpr(cons)
      val finalState = state.setTheory(BoolTheory()).setRex(NameEx(eqPred))
      rewriter.coerce(finalState, state.theory)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
  }
}
