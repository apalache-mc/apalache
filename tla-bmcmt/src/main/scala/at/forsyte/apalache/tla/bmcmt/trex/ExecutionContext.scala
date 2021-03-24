package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter
import at.forsyte.apalache.tla.bmcmt.rewriter.Recoverable
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext

/**
 * A context that is used by TransitionExecutor. By default, a context is not thread-safe,
 * that is, you should have one context per thread.
 * IncrementalExecutorContext is the simplest implementation.
 *
 * @author Igor Konnov
 */
trait ExecutionContext[SnapshotT] extends Recoverable[SnapshotT] {
  type SnapT = SnapshotT

  def rewriter: SymbStateRewriter

  def solver: SolverContext = rewriter.solverContext

  /**
   * Dispose the resources that are associated with the context: rewriter, solver, type finder.
   * The context should not be used after the call to dispose.
   */
  def dispose(): Unit
}
