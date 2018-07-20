package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FailPredT, UnknownT}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}

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
        val finalState = state
          .setRex(NameEx(rewriter.solverContext.trueConst))
          .setTheory(BoolTheory())
        rewriter.coerce(finalState, state.theory)

      case OperEx(TlcOper.assert, value, ValEx(TlaStr(message))) =>
        val valueState = rewriter.rewriteUntilDone(state.setRex(value).setTheory(BoolTheory()))
        // introduce an unknown value for the outcome of assert, since this value may be unified in IF-THEN-ELSE
        var arena = valueState.arena.appendCell(UnknownT())
        val result = arena.topCell
        // introduce a new failure predicate
        arena = arena.appendCell(FailPredT())
        val failPred = arena.topCell
        rewriter.addMessage(failPred.id, "Assertion error: " + message)
        val assertion = valueState.ex
        val constraint = tla.impl(failPred.toNameEx, tla.not(assertion))
        rewriter.solverContext.assertGroundExpr(constraint)
        // return isReachable. If there is a model M s.t. M |= isReachable, then M |= failPred allows us
        // to check, whether the assertion is violated or not
        val finalState = valueState.setArena(arena)
          .setRex(result.toNameEx)
          .setTheory(BoolTheory())
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
