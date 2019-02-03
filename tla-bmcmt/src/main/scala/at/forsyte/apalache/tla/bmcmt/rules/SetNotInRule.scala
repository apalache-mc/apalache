package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}

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
          state.setTheory(CellTheory()).setRex(OperEx(TlaSetOper.in, cand, set))
        val nextState = rewriter.rewriteUntilDone(inState)
        val finalState = nextState.setRex(OperEx(TlaBoolOper.not, nextState.ex))
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
