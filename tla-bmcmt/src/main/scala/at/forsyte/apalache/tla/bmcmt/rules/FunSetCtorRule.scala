package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FinFunSetT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

/**
  * This rule constructs a cell for a function set [S -> T]. Since we are not expanding function sets by default,
  * this cell is just pointing to S as its domain and to T as its co-domain.
  *
  * @author Igor Konnov
  */
class FunSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _                               => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.funSet, domEx, cdmEx) =>
        // switch to cell theory
        var nextState = rewriter.rewriteUntilDone(state.setRex(domEx))
        val dom = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(cdmEx))
        val cdm = nextState.asCell
        val arena =
          nextState.arena.appendCell(FinFunSetT(dom.cellType, cdm.cellType))
        val newCell = arena.topCell
        val newArena = arena
          .setDom(newCell, dom)
          .setCdm(newCell, cdm)
        state.setArena(newArena).setRex(newCell.toNameEx)

      case _ =>
        throw new RewriterException(
          "%s is not applicable".format(getClass.getSimpleName),
          state.ex
        )
    }
  }
}
