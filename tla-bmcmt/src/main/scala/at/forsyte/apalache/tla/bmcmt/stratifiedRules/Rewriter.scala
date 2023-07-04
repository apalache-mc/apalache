package at.forsyte.apalache.tla.bmcmt.stratifiedRules

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * <p>A trait for a state rewriter. The main purpose of this trait is to rewrite a TLA+ expression into a graph of cells
 * (Arena).
 *
 * <p> As a by-product, implementations may use a [[at.forsyte.apalache.tla.bmcmt.smt.SolverContext]] and produce SMT
 * constraints over the computed Arena cells.</p>
 *
 * <p>This is the central access point for the rewriting rules.</p>
 *
 * @author
 *   Jure Kukovec
 */
trait Rewriter {

  /**
   * Fully rewrite a TlaEx into an ArenaCell.
   *
   * Any Binding or Arena changes made as part of the rewriting are returned in the RewriterScope part of the return
   * tuple, while the ArenaCell part of the return is the cell representation of the input TlaEx.
   */
  def rewrite(ex: TlaEx)(startingScope: RewriterScope): (RewriterScope, ArenaCell)

  /**
   * Fully rewrite a TlaEx into an ArenaCell.
   *
   * Any Binding or Arena changes made as part of the rewriting are returned in the RewriterScope part of the return
   * tuple, while the ArenaCell part of the return is the cell representation of the input TlaEx.
   */
  def assert(ex: TlaEx): Unit

}
