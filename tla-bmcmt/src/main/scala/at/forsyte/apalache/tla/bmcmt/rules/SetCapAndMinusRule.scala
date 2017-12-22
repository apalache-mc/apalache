package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * Implements the rules SE-SET-CAP1 and SE-SET-DIFF1, that is, set intersection and set difference respectively.
  *
  * @author Igor Konnov
  */
class SetCapAndMinusRule(rewriter: SymbStateRewriter) extends RewritingRule {

  private object OpEnum extends Enumeration {
    val CAP, MINUS = Value
  }

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.cap, _*) => true
      case OperEx(TlaSetOper.setminus, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.cap, leftSet, rightSet) =>
        val finalState: SymbState = intersectOrDiff(OpEnum.CAP, state, leftSet, rightSet)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case OperEx(TlaSetOper.setminus, leftSet, rightSet) =>
        val finalState: SymbState = intersectOrDiff(OpEnum.MINUS, state, leftSet, rightSet)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def intersectOrDiff(op: OpEnum.Value, state: SymbState, leftSet: TlaEx, rightSet: TlaEx): SymbState = {
    val leftState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(leftSet))
    val rightState = rewriter.rewriteUntilDone(leftState.setTheory(CellTheory()).setRex(rightSet))
    val leftSetCell = leftState.arena.findCellByNameEx(leftState.ex)
    val rightSetCell = rightState.arena.findCellByNameEx(rightState.ex)
    val leftElemCells = leftState.arena.getHas(leftSetCell)
    val rightElemCells = rightState.arena.getHas(rightSetCell)
    // introduce a new set
    val arena = rightState.arena.appendCell(leftSetCell.cellType.join(rightSetCell.cellType))
    val resultSetCell = arena.topCell

    // add new arena edges
    val newArena =
      op match {
        case OpEnum.CAP =>
          if (leftElemCells.isEmpty && rightElemCells.isEmpty) {
            arena // don't add anything, the intersection is empty
          } else {
            (leftElemCells ++ rightElemCells).foldLeft(arena)((a, e) => a.appendHas(resultSetCell, e))
          }

        case OpEnum.MINUS =>
          leftElemCells.foldLeft(arena)((a, e) => a.appendHas(resultSetCell, e))
      }

    // add SMT constraints
    val newState:SymbState =
      if (leftElemCells.nonEmpty) {
        def mkConsFun = if (op == OpEnum.CAP) overlap _ else noOverlap _

        def overlapOrNot(st: SymbState, elem: ArenaCell): SymbState = {
          if (op == OpEnum.CAP)
            overlap(st, resultSetCell, leftSetCell, elem, rightSetCell, rightElemCells)
          else
            noOverlap(st, resultSetCell, leftSetCell, elem, rightSetCell, rightElemCells)
        }

        // for every element in the left set, there must be an element in the right set (or no element in case of diff)
        val afterLeft = leftElemCells.foldLeft(rightState) (overlapOrNot)

        if (op == OpEnum.CAP && rightElemCells.nonEmpty) {
          def over(st: SymbState, elem: ArenaCell): SymbState = {
            overlap(st, resultSetCell, rightSetCell, elem, leftSetCell, leftElemCells)
          }
          // for every element in the right set, there must be an element in the left set
          rightElemCells.foldLeft(afterLeft) (over)
        } else {
          afterLeft
        }
      } else {
        rightState
      }

    // that's it
    newState.setTheory(CellTheory())
      .setArena(newArena).setRex(resultSetCell.toNameEx)
  }

  private def in(e: ArenaCell, s: ArenaCell) = OperEx(TlaSetOper.in, e.toNameEx, s.toNameEx)

  // TODO: these are common functions, move them to TlaExBuilder
  private def and(es: TlaEx*) = OperEx(TlaBoolOper.and, es: _*)

  private def or(es: TlaEx*) = OperEx(TlaBoolOper.or, es: _*)

  private def not(e: TlaEx) = OperEx(TlaBoolOper.not, e)

  // see SE-SET-CAP1 for a description
  private def overlap(state: SymbState, capSet: ArenaCell, set: ArenaCell, elem: ArenaCell,
                      otherSet: ArenaCell, otherElems: List[ArenaCell]): SymbState = {
    // produce equality constraints first
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, otherElems.map(e => (e, elem)))

    // now we can use SMT equality
    def existsOther(otherElem: ArenaCell) =
      and(in(otherElem, otherSet), rewriter.lazyEq.safeEq(otherElem, elem))

    val cons =
      tla.equiv(in(elem, capSet),
        and(in(elem, set), or(otherElems.map(existsOther): _*)))

    eqState.solverCtx.assertGroundExpr(cons)
    eqState
  }

  // see SE-SET-DIFF for a description
  private def noOverlap(state: SymbState, diffSet: ArenaCell, set: ArenaCell, elem: ArenaCell,
                        otherSet: ArenaCell, otherElems: List[ArenaCell]): SymbState = {
    // produce equality constraints first
    val eqState = rewriter.lazyEq.cacheEqConstraints(state, otherElems.map(e => (e, elem)))

    // now we can use SMT equality
    def noOther(otherElem: ArenaCell) =
      or(not(in(otherElem, otherSet)), not(rewriter.lazyEq.safeEq(otherElem, elem)))

    val cons =
      tla.equiv(in(elem, diffSet),
        and(in(elem, set), and(otherElems.map(noOther): _*)))

    eqState.solverCtx.assertGroundExpr(cons)
    eqState
  }
}
