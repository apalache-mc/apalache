package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetType, UnknownType}
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules: SE-SET-CTOR[1-2].
  *
  * @author Igor Konnov
   */
class SetCtorRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.enumSet, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.enumSet, elems @ _*) =>
        val (newState: SymbState, newEs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, elems)
        val cells = newEs.map(e => state.arena.findCellByName(cellToString(e)))
        // FIXME: introduce a sum type for the elements?
        var arena = newState.arena.appendCell(FinSetType(UnknownType()))
        val newCell = arena.topCell
        arena = cells.foldLeft(arena)((a, e) => a.appendHas(newCell, e))
        def addIn(c: ArenaCell): Unit = {
          val inExpr = OperEx(TlaSetOper.in, c.toNameEx, newCell.toNameEx)
          state.solverCtx.assertCellExpr(inExpr)
        }
        cells.foreach(addIn)
        state.setArena(arena).setRex(newCell.toNameEx)


      case _ =>
        throw new RewriterException("SetCtorRule is not applicable")
    }
  }
}
