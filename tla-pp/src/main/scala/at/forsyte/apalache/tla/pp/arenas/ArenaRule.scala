package at.forsyte.apalache.tla.pp.arenas

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * @author
 *   Jure Kukovec
 */
trait ArenaRule {
  def isApplicable(ex: TlaEx): ArenaComputationInternalState[Boolean]

  def apply(tlaEx: TlaEx): ArenaComputation
}
