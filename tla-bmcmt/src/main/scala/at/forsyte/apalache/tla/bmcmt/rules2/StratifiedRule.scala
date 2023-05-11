package at.forsyte.apalache.tla.bmcmt.rules2

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * * A single rewriting rule that implements operational semantics.
 *
 * A rule may be parameterized by `T`, which defines the sort of supplementary information passed between the
 * `buildArena` and `addConstraints` methods, for the purpose of generating SMT constraints. If no such information is
 * necessary, `T = Unit`.
 *
 * @author
 *   Jure Kukovec
 */
trait StratifiedRule[T] {
  def isApplicable(ex: TlaEx, scope: RewriterScope): Boolean

  /**
   * Returns a triple `(scope,cell,aux)`, where
   *   - `scope` contains the new Arena adn Binding generated from `ex`.
   *   - `cell` is an ArenaCell representation of `ex`
   *   - `aux` contains miscellaneous data, which may be used in `addConstraints` in the process of constraint
   *     generation.
   *
   * This method promises not to generate constraints as a side-effect.
   */
  def buildArena(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell, T)

  /**
   * Given the output of `buildArena`, generates SMT constraints as a side-effect.
   */
  def addConstraints(scope: RewriterScope, cell: ArenaCell, auxData: T): Unit

  def apply(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell) = {
    val (scope, exprCell, auxCells) = buildArena(ex)(startingScope)
    addConstraints(scope, exprCell, auxCells)
    (scope, exprCell)
  }

}
