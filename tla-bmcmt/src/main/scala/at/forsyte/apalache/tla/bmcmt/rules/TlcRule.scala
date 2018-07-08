package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.FailPredT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlcOper

/**
  * Implements the rules for TLC operators.
  *
  * @author Igor Konnov
   */
class TlcRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlcOper.print, _, _) => true
      case OperEx(TlcOper.printT, _) => true
      case OperEx(TlcOper.assert, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlcOper.print, _, _)
           | OperEx(TlcOper.printT, _) =>
        rewriter.coerce(state.setRex(tla.bool(true)).setTheory(BoolTheory()), state.theory)

      case OperEx(TlcOper.assert, value, _) =>
        val valueState = rewriter.rewriteUntilDone(state.setRex(value).setTheory(BoolTheory()))
        // introduce a new failure predicate
        val newArena = valueState.arena.appendCell(FailPredT())
        val failPred = newArena.topCell
        rewriter.solverContext.assertGroundExpr(tla.equiv(failPred.toNameEx, tla.not(valueState.ex)))
        // return true, the assertion is encoded with a failure predicate.
        val finalState = valueState.setArena(newArena).setRex(tla.bool(true)).setTheory(BoolTheory())
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
