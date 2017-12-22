package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.FinFunSetT
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rule: SE-FUNSET1, that is, constructs a function set [S -> T].
  *
  * @author Igor Konnov
   */
class FunSetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.funSet, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.funSet, domEx, cdmEx) =>
        // switch to cell theory
        val (newState: SymbState, cells: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), List(domEx, cdmEx))

        val dom = newState.arena.findCellByNameEx(cells.head)
        val cdm = newState.arena.findCellByNameEx(cells.tail.head)
        val arena = newState.arena.appendCell(FinFunSetT(dom.cellType, cdm.cellType))
        val newCell = arena.topCell
        val newArena = arena
          .setDom(newCell, dom)
          .setCdm(newCell, cdm)
        val finalState =
          state.setArena(newArena).setRex(newCell.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
