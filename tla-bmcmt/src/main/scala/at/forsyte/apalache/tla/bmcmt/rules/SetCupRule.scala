package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.util.Prod2SeqIterator
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

/**
  * Implements the rule: SE-SET-CUP1, that is, a union of two sets.
  * In the first encoding, we used a linear number of `in` queries.
  * However, this happens to be unsound, and we need a quadratic number of queries.
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
        val leftElems = leftState.arena.getHas(leftSetCell)
        val rightElems = rightState.arena.getHas(rightSetCell)
        // introduce a new set
        val newType = types.unify(leftSetCell.cellType, rightSetCell.cellType)
        if (newType.isEmpty) {
          throw new TypeException(s"Failed to unify types ${leftSetCell.cellType}"
            + " and ${rightSetCell.cellType} when rewriting ${state.ex}")
        }
        var arena = rightState.arena.appendCell(newType.get)
        val newSetCell = arena.topCell
        arena = (leftElems ++ rightElems).foldLeft(arena)((a, e) => a.appendHas(newSetCell, e))

        // require each cell to be in one of the two sets
        def addCellCons(thisSet: ArenaCell, otherSet: ArenaCell, otherCells: Seq[ArenaCell], thisElem: ArenaCell): Unit = {
          def mkInAndEq(otherElem: ArenaCell) =
            tla.and(tla.in(otherElem.toNameEx, otherSet.toNameEx),
                    rewriter.lazyEq.safeEq(otherElem, thisElem))
          val inOther = tla.or(otherCells map mkInAndEq :_*)
          val inThis = tla.in(thisElem.toNameEx, thisSet.toNameEx)
          val inCup = tla.in(thisElem.toNameEx, newSetCell.toNameEx)
          val iff = tla.equiv(inCup, tla.or(inThis, inOther))
          rewriter.solverContext.assertGroundExpr(iff)
        }

        // Add equality constraints, e.g., for ({1} \ {1}) \cup {1}. Otherwise, we might require equal cells to be
        // inside and outside the resulting set
        val prodIter = new Prod2SeqIterator(leftElems, rightElems)
        val eqState = rewriter.lazyEq.cacheEqConstraints(rightState.setArena(arena), prodIter.toSeq)

        // bugfix: we have to compare the elements in both sets and thus to introduce a quadratic number of constraints
        // add SMT constraints
        leftElems.foreach(addCellCons(leftSetCell, rightSetCell, rightElems, _))
        rightElems.foreach(addCellCons(rightSetCell, leftSetCell, leftElems, _))

        // that's it
        val finalState = eqState.setTheory(CellTheory()).setRex(newSetCell.toNameEx)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
