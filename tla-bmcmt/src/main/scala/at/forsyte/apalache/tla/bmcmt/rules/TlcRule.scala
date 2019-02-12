package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.FailPredT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

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
      case OperEx(TlcOper.colonGreater, _, _) => true
      case OperEx(TlcOper.atat, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlcOper.print, _, _)
           | OperEx(TlcOper.printT, _) =>
        val finalState = state
          .setRex(NameEx(SolverContext.trueConst))
          .setTheory(BoolTheory())
        rewriter.coerce(finalState, state.theory)

      case OperEx(TlcOper.assert, value, ValEx(TlaStr(message))) =>
        rewriteAssert(state, value, message)

      case OperEx(TlcOper.colonGreater, arg, res) => // a :> b
        state.setRex(tla.tuple(arg, res)) // just construct a tuple

      case OperEx(TlcOper.atat, funEx, pairEx) =>
        // f @@ a :> b, the type checker should take care of types
        extendFun(state, funEx, pairEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def extendFun(state: SymbState, funEx: TlaEx, pairEx: TlaEx): SymbState = {
    def solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = rewriter.rewriteUntilDone(state.setRex(funEx).setTheory(CellTheory()))
    val funCell = nextState.asCell
    val relation = nextState.arena.getCdm(funCell)
    val relationCells = nextState.arena.getHas(relation)
    nextState = rewriter.rewriteUntilDone(nextState.setRex(pairEx).setTheory(CellTheory()))
    val newPair = nextState.asCell
    nextState = nextState.appendArenaCell(funCell.cellType)
    val newFunCell = nextState.arena.topCell
    nextState = nextState.appendArenaCell(relation.cellType)
    val newRelation = nextState.arena.topCell
    nextState = nextState.setArena(nextState.arena.setCdm(newFunCell, newRelation)
      .appendHas(newRelation, newPair +: relationCells))
    // the new pair unconditionally belongs to the new cell
    solverAssert(tla.in(newPair.toNameEx, newRelation.toNameEx))
    for (oldPair <- relationCells) {
      val inOld = tla.in(oldPair.toNameEx, relation.toNameEx)
      val inNew = tla.in(oldPair.toNameEx, newRelation.toNameEx)
      solverAssert(tla.equiv(inNew, inOld))
    }

    nextState.setRex(newFunCell.toNameEx).setTheory(CellTheory())
  }

  private def rewriteAssert(state: SymbState, value: TlaEx, message: String) = {
    val valueState = rewriter.rewriteUntilDone(state.setRex(value).setTheory(BoolTheory()))
    // introduce a new failure predicate
    var arena = state.arena.appendCell(FailPredT())
    val failPred = arena.topCell
    rewriter.addMessage(failPred.id, "Assertion error: " + message)
    val assertion = valueState.ex
    val constraint = tla.impl(failPred.toNameEx, tla.not(assertion))
    rewriter.solverContext.assertGroundExpr(constraint)
    // return isReachable. If there is a model M s.t. M |= isReachable, then M |= failPred allows us
    // to check, whether the assertion is violated or not
    val finalState = valueState.setArena(arena)
      .setRex(NameEx(SolverContext.trueConst)) // if you need a value of a type different from bool, use TypedAssert
      .setTheory(BoolTheory())
    rewriter.coerce(finalState, state.theory)
  }
}
