package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements logical negation.
  *
  * @author Igor Konnov
  */
class NegRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val substRule = new SubstRule(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.not, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.not, ex: TlaEx) =>
        val newState = rewriter.rewriteUntilDone(state.setRex(ex).setTheory(BoolTheory()))
        val pred = rewriter.solverContext.introBoolConst()
        rewriter.solverContext.assertGroundExpr(tla.eql(tla.not(tla.name(pred)), newState.ex))
        val finalState = newState.setRex(tla.name(pred))
        // coerce back, if needed
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
