package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * @author
 *   Jure Kukovec
 */
trait StratifiedRule[T] {
  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean

  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, T)

  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: T): Unit

  def apply(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell) = {
    val (scope, exprCell, auxCells) = buildArena(ex)(startingScope)
    addConstraints(scope, exprCell, auxCells)
    (scope, exprCell)
  }

}
