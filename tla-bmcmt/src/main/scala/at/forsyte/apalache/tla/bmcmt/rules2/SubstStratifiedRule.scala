package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{NameEx, TlaEx}
import at.forsyte.apalache.tla.pp.TlaInputError
import com.typesafe.scalalogging.LazyLogging

class SubstStratifiedRule extends StratifiedRule[Unit] with LazyLogging {
  override def isApplicable(ex: TlaEx, scop: RewriterScope): Boolean = ex match {
    case NameEx(x) =>
      // make sure that x is not an SMT constant, but a variable name
      !ArenaCell.isValidName(x)

    case _ => false
  }

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, Unit) = ex match {
    case NameEx(x) =>
      val binding = startingScope.binding
      if (binding.contains(x)) {
        (startingScope, binding(x), ())
      } else {
        logger.error("This error may show up when CONSTANTS are not initialized.")
        logger.error("Check the manual: https://apalache.informal.systems/docs/apalache/parameters.html")
        throw new TlaInputError(s"${getClass.getSimpleName}: Variable $x is not assigned a value")
      }

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), ex)
  }

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: Unit): Unit = ()
}
