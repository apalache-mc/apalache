package at.forsyte.apalache.tla.pp.arenas.rules

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.pp.arenas.{getVarCtx, ArenaComputation, ArenaComputationInternalState, ArenaRule}
import scalaz.Scalaz._
import scalaz._

/**
 * @author
 *   Jure Kukovec
 */
class SubstArenaRule extends ArenaRule {
  override def isApplicable(tlaEx: TlaEx): ArenaComputationInternalState[Boolean] = (tlaEx match {
    case NameEx(x) => !ArenaCell.isValidName(x)
    case _         => false
  }).point[ArenaComputationInternalState]

  override def apply(tlaEx: TlaEx): ArenaComputation = tlaEx match {
    case NameEx(x) =>
      getVarCtx.map {
        _.getOrElse(
            x,
            throw new Exception(s"${getClass.getSimpleName}: Variable $x is not assigned a value"),
        )
      }

    case _ =>
      throw new Exception("%s is not applicable".format(getClass.getSimpleName))
  }
}
