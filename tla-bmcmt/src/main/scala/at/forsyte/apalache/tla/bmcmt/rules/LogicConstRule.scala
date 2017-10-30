package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.values.{TlaFalse, TlaTrue}

/**
  * Implements the rules: SE-LOGIC-CONST{1,2}
   */
class LogicConstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.rex match {
      case TlaRex(ValEx(TlaFalse)) => true
      case TlaRex(ValEx(TlaTrue)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState, dir: SymbStateRewriter.SearchDirection): SymbState = {
    state.rex match {
      case TlaRex(ValEx(TlaFalse)) =>
        state.setRex(PredRex(state.solverCtx.predFalse()))

      case TlaRex(ValEx(TlaTrue)) =>
        state.setRex(PredRex(state.solverCtx.predTrue()))

      case _ =>
        throw new RewriterException("LogicConstRule is not applicable")
    }
  }
}
