package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * @author
 *   Jure Kukovec
 */
trait Rewriter {

  def rewrite(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell)

}
