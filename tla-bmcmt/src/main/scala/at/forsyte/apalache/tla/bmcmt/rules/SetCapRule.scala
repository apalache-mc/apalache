package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rule: SE-SET-CAP1, that is, an intersection of two sets.
  *
  * @author Igor Konnov
  */
class SetCapRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.cap, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.cap, leftSet, rightSet) =>
        // rewrite the set expressions into memory cells
        val leftState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(leftSet))
        val rightState = rewriter.rewriteUntilDone(leftState.setTheory(CellTheory()).setRex(rightSet))
        val leftSetCell = leftState.arena.findCellByNameEx(leftState.ex)
        val rightSetCell = rightState.arena.findCellByNameEx(rightState.ex)
        val leftElemCells = leftState.arena.getHas(leftSetCell)
        val rightElemCells = rightState.arena.getHas(rightSetCell)
        // introduce a new set
        val arena = rightState.arena.appendCell(leftSetCell.cellType.join(rightSetCell.cellType))
        val capSetCell = arena.topCell
        val newArena = (leftElemCells ++ rightElemCells).foldLeft(arena)((a, e) => a.appendHas(capSetCell, e))

        if (leftElemCells.nonEmpty && rightElemCells.nonEmpty) {
          for (leftElem <- leftElemCells)
            newArena.solverContext
              .assertGroundExpr(overlap(newArena, capSetCell, leftSetCell, leftElem, rightSetCell, rightElemCells))

          for (rightElem <- rightElemCells)
            newArena.solverContext
              .assertGroundExpr(overlap(newArena, capSetCell, rightSetCell, rightElem, leftSetCell, leftElemCells))
        }

        // that's it
        val finalState =
          rightState.setTheory(CellTheory())
            .setArena(newArena).setRex(capSetCell.toNameEx)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case _ =>
        throw new RewriterException("SetCapRule is not applicable")
    }
  }

  // see SE-SET-CAP1 for a description
  private def overlap(arena: Arena, capSet: ArenaCell, set: ArenaCell, elem: ArenaCell,
                      otherSet: ArenaCell, otherElems: List[ArenaCell]) = {
    def in(e: ArenaCell, s: ArenaCell) = OperEx(TlaSetOper.in, e.toNameEx, s.toNameEx)
    def eq(l: ArenaCell, r: ArenaCell) = arena.lazyEquality.mkEquality(arena, l, r)
    def and(es: TlaEx*) = OperEx(TlaBoolOper.and, es: _*)
    def or(es: TlaEx*) = OperEx(TlaBoolOper.or, es: _*)

    def existsOther(otherElem: ArenaCell) =
      and(in(otherElem, otherSet), eq(otherElem, elem))

    OperEx(TlaBoolOper.equiv,
      in(elem, capSet),
      and(in(elem, set), or(otherElems.map(existsOther): _*)))
  }
}
