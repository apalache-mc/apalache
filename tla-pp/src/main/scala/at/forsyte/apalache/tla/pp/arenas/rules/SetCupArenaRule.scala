package at.forsyte.apalache.tla.pp.arenas.rules

import at.forsyte.apalache.tla.bmcmt.PtrUtil
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, TlaType1}
import at.forsyte.apalache.tla.pp.arenas.{ArenaComputationInternalState, _}
import scalaz.Scalaz._
import scalaz._

/**
 * @author
 *   Jure Kukovec
 */
class SetCupArenaRule(rewriter: ArenaRewriter) extends ArenaRule {
  override def isApplicable(tlaEx: TlaEx): ArenaComputationInternalState[Boolean] = (tlaEx match {
    case OperEx(TlaSetOper.cup, _*) => true
    case _                          => false
  }).point[ArenaComputationInternalState]

  override def apply(tlaEx: TlaEx): ArenaComputation = tlaEx match {
    case OperEx(TlaSetOper.cup, leftSet, rightSet) =>
      for {
        leftSetCell <- rewriter.rewrite(leftSet)
        rightSetCell <- rewriter.rewrite(rightSet)
        arena <- getArena

        leftPtrs = arena.getHas(leftSetCell)
        rightPtrs = arena.getHas(rightSetCell)
        unionElemPtrs = PtrUtil.mergePtrsByCellMap(leftPtrs ++ rightPtrs)

        retCell <- newCell(tlaEx.ID, TlaType1.fromTypeTag(tlaEx.typeTag))
        _ <- modify[ArenaComputationContext] { s =>
          s.copy(arena = s.arena.appendHas(retCell, unionElemPtrs: _*))
        }
      } yield retCell

    case _ => throw new Exception("%s is not applicable".format(getClass.getSimpleName))
  }

}
