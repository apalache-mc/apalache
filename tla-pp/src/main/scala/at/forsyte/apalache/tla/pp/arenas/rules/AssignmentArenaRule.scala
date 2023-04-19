package at.forsyte.apalache.tla.pp.arenas.rules

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.bmcmt.PureArena.cellTrue
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}
import at.forsyte.apalache.tla.pp.arenas._
import scalaz.Scalaz._
import scalaz._

/**
 * @author
 *   Jure Kukovec
 */
class AssignmentArenaRule(rewriter: ArenaRewriter) extends ArenaRule {

  override def isApplicable(tlaEx: TlaEx): ArenaComputationInternalState[Boolean] =
    getVarCtx.map { ctx =>
      tlaEx match {
        case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), _) =>
          !ArenaCell.isValidName(name) && !ctx.contains(name + "'")
        case _ => false

      }
    }

  override def apply(tlaEx: TlaEx): ArenaComputation = tlaEx match {
    // general case
    case OperEx(ApalacheOper.assign, OperEx(TlaActionOper.prime, NameEx(name)), rhs) =>
      for {
        rhsCell <- rewriter.rewrite(rhs)
        _ <- bind(name + "'", rhsCell)
        arena <- getArena
      } yield cellTrue(arena)

    case _ =>
      throw new Exception("%s is not applicable".format(getClass.getSimpleName))
  }

}
