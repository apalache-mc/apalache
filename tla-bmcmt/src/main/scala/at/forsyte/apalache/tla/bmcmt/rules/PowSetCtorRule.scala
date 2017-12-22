package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.PowSetT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

/**
  * Implements the rule: SE-SUBSET1, that is, constructs the powerset SUBSET S for a set S.
  *
  * @author Igor Konnov
   */
class PowSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.powerset, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.powerset, setEx) =>
        // switch to cell theory
        val nextState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))

        val dom = nextState.arena.findCellByNameEx(nextState.ex)
        val arena = nextState.arena.appendCell(PowSetT(dom.cellType))
        val powSetCell = arena.topCell
        val newArena = arena.setDom(powSetCell, dom)
        val finalState =
          state.setArena(newArena).setRex(powSetCell.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
