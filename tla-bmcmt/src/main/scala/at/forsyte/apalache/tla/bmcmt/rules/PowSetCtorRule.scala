package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.PowSetT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

/**
 * Rewrites the powerset SUBSET S for a set S.
 *
 * @author Igor Konnov
 */
class PowSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.powerset, _) => true
      case _                              => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.powerset, setEx) =>
        // switch to cell theory
        var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))

        val dom = nextState.arena.findCellByNameEx(nextState.ex)
        nextState = nextState.updateArena(_.appendCell(PowSetT(dom.cellType)))
        val powSetCell = nextState.arena.topCell
        nextState = nextState.updateArena(_.setDom(powSetCell, dom))
        nextState.setRex(powSetCell.toNameEx)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
