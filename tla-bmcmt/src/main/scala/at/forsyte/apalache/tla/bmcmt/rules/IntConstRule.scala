package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}

/**
  * Implements the rule SE-INT-CONST.
  *
  * @author Igor Konnov
  */
class IntConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaInt(_)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaInt(n)) =>
        val intConst = state.solverCtx.introIntConst()
        state.solverCtx.assertGroundExpr(OperEx(TlaOper.eq, NameEx(intConst), ValEx(TlaInt(n))))
        val finalState =
          state.setTheory(IntTheory()).setRex(NameEx(intConst))
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("IntConstRule is not applicable")
    }
  }
}
