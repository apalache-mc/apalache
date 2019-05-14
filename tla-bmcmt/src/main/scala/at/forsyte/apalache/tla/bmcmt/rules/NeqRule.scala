package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Implements the rule: SE-NE1.
  *
  * @author Igor Konnov
  */
class NeqRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaOper.ne, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaOper.ne, left, right) =>
        val eqState =
          state.setRex(OperEx(TlaOper.eq, left, right))
        val nextState = rewriter.rewriteUntilDone(eqState)
        val finalState =
          if (NameEx(SolverContext.falseConst) == nextState.ex) {
            nextState.setRex(NameEx(SolverContext.trueConst))
          } else if (NameEx(SolverContext.trueConst) == nextState.ex) {
            nextState.setRex(NameEx(SolverContext.falseConst))
          } else {
            val neState =  nextState.setRex(OperEx(TlaBoolOper.not, nextState.ex))
            rewriter.rewriteUntilDone(neState)
          }
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
