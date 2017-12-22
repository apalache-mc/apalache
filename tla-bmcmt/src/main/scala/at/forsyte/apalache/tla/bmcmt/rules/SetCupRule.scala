package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}

/**
  * Implements the rule: SE-SET-CUP1, that is, a union of two sets.
  *
  * @author Igor Konnov
  */
class SetCupRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.cup, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.cup, leftSet, rightSet) =>
        // rewrite the set expressions into memory cells
        val leftState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(leftSet))
        val rightState = rewriter.rewriteUntilDone(leftState.setTheory(CellTheory()).setRex(rightSet))
        val leftSetCell = leftState.arena.findCellByNameEx(leftState.ex)
        val rightSetCell = rightState.arena.findCellByNameEx(rightState.ex)
        val leftElemCells = leftState.arena.getHas(leftSetCell)
        val rightElemCells = rightState.arena.getHas(rightSetCell)
        // introduce a new set
        val arena = rightState.arena.appendCell(leftSetCell.cellType.join(rightSetCell.cellType))
        val newSetCell = arena.topCell
        val newArena = (leftElemCells ++ rightElemCells).foldLeft(arena)((a, e) => a.appendHas(newSetCell, e))

        // require each cell to be in one of the two sets
        def addCellCons(elemCell: ArenaCell): Unit = {
          val inCupSet = OperEx(TlaSetOper.in, elemCell.toNameEx, newSetCell.toNameEx)
          val inLeftSet = OperEx(TlaSetOper.in, elemCell.toNameEx, leftSetCell.toNameEx)
          val inRightSet = OperEx(TlaSetOper.in, elemCell.toNameEx, rightSetCell.toNameEx)
          val inLeftOrRight = OperEx(TlaBoolOper.or, inLeftSet, inRightSet)
          val ifAndOnlyIf = OperEx(TlaOper.eq, inCupSet, inLeftOrRight)
          rightState.solverCtx.assertGroundExpr(ifAndOnlyIf)
        }

        // add SMT constraints
        for (cell <- leftElemCells ++ rightElemCells)
          addCellCons(cell)

        // that's it
        val finalState =
          rightState.setTheory(CellTheory())
            .setArena(newArena).setRex(newSetCell.toNameEx)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
