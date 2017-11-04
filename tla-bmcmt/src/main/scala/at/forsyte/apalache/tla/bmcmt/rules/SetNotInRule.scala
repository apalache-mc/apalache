package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Implements the rules: SE-SET-NOTIN1.
  *
  * @author Igor Konnov
  */
class SetNotInRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.notin, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.notin, cand, set) =>
        val inState =
          state.setTheory(BoolTheory()).setRex(OperEx(TlaSetOper.in, cand, set))
        val nextState = rewriter.rewriteUntilDone(inState)
        val finalState =
          if (NameEx(state.solverCtx.falseConst) == nextState.ex) {
            nextState.setRex(NameEx(state.solverCtx.trueConst))
          } else if (NameEx(state.solverCtx.trueConst) == nextState.ex) {
            nextState.setRex(NameEx(state.solverCtx.falseConst))
          } else {
            nextState.setRex(OperEx(TlaBoolOper.not, nextState.ex))
          }
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("SetNotInRule is not applicable")
    }
  }
}
