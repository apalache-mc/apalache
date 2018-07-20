package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Implements an implication A => B by rewriting it to ~A \/ B.
  *
  * @author Igor Konnov
  */
class EquivRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val substRule = new SubstRule(rewriter)
  private val simplifier = new ConstSimplifier()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.equiv, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.equiv, left, right) =>
        val leftState = rewriter.rewriteUntilDone(state.setRex(left).setTheory(BoolTheory()))
        val rightState = rewriter.rewriteUntilDone(leftState.setRex(right).setTheory(BoolTheory()))
        val result = rewriter.solverContext.introBoolConst()
        rewriter.solverContext.assertGroundExpr(tla.eql(NameEx(result), tla.equiv(leftState.ex, rightState.ex)))
        val finalState = rightState.setRex(NameEx(result)).setTheory(BoolTheory())
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
