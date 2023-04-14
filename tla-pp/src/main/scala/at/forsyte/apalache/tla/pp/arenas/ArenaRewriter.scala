package at.forsyte.apalache.tla.pp.arenas

import at.forsyte.apalache.tla.lir.TlaEx

/**
 * @author
 *   Jure Kukovec
 */
trait ArenaRewriter {
  def rewrite(tlaEx: TlaEx): ArenaComputation
}
