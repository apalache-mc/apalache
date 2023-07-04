package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.PtrUtil
import at.forsyte.apalache.tla.bmcmt.types.CellT
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
 * Rewrites X \cup Y, that is, a union of two sets (not UNION).
 *
 * @author
 *   Jure Kukovec
 */
class SetCupStratifiedRule(rewriter: Rewriter) extends StratifiedRule[Unit] {

  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean = ex match {
    case OperEx(TlaSetOper.cup, _*) => true
    case _                          => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, Unit) =
    ex match {
      case OperEx(TlaSetOper.cup, leftSet, rightSet) =>
        // rewrite the set expressions into memory cells
        val (postLhsScope, leftSetCell) = rewriter.rewrite(leftSet)(startingScope)
        val (postRhsScope, rightSetCell) = rewriter.rewrite(rightSet)(postLhsScope)

        val leftPtrs = postRhsScope.arena.getHas(leftSetCell)
        val rightPtrs = postRhsScope.arena.getHas(rightSetCell)

        // Fixed pointers dominate, if no pointer is fixed we take the disjunction of the smt constraints
        val unionElemPtrs: Seq[ElemPtr] = PtrUtil.mergePtrsByCellMap(leftPtrs ++ rightPtrs)

        // introduce a new set
        val newType = CellT.fromTypeTag(ex.typeTag)
        val arenaWithNewCell = postRhsScope.arena.appendCell(newType)
        val newSetCell = arenaWithNewCell.topCell
        val arenaWithHasEdges = arenaWithNewCell.appendHas(newSetCell, unionElemPtrs: _*)

        (postRhsScope.copy(arena = arenaWithHasEdges), newSetCell, (leftSetCell, rightSetCell))
      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), ex)
    }

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: Unit): Unit =
    scope.arena.getHas(cell).foreach { ptr =>
      // assert here
      println(s"Assert: ${ptr.toSmt.build}")
    }

}
