package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.smt.RecordingSolverContext
import at.forsyte.apalache.tla.bmcmt.{SymbStateRewriter, SymbStateRewriterImpl}
import com.typesafe.scalalogging.LazyLogging

/**
 * An executor context for an offline SMT solver.
 *
 * @param rewriter an expression rewriter
 */
class OfflineExecutionContext(var rewriter: SymbStateRewriter)
    extends ExecutionContext[OfflineExecutionContextSnapshot] with LazyLogging {

  /**
   * Create a snapshot of the context. This method is non-destructive, that is,
   * the context may be used after a snapshot has been made.
   *
   * @return a snapshot
   */
  override def snapshot(): OfflineExecutionContextSnapshot = {
    val rs = rewriter.snapshot()
    val smtLog = rewriter.solverContext.asInstanceOf[RecordingSolverContext].extractLog()
    logger.debug("Offline snapshot has %d entries".format(smtLog.lengthRec))
    new OfflineExecutionContextSnapshot(rewriter.solverContext.config, rs, smtLog, typeFinder.varTypes)
  }

  /**
   * <p>Recover the context from a snapshot that was created earlier.
   * It is up to the implementation to require, whether the snapshot should be created
   * within the same context.</p>
   *
   * <p>This method recovers the snapshot in place, so the context gets overwritten
   * with the snapshot contents. Note that a call recover(A) renders useless the
   * snapshots that were created in the time frame between A = snapshot()
   * and recover(A).</p>
   *
   * @param snapshot a snapshot
   * @throws IllegalStateException when recovery is impossible
   */
  override def recover(snapshot: OfflineExecutionContextSnapshot): Unit = {
    val solver = RecordingSolverContext.createZ3(Some(snapshot.smtLog), snapshot.solverConfig)
    // TODO: issue #105, remove references to SolverContext, so recovery becomes less of a hack
    val newRewriter = new SymbStateRewriterImpl(solver, typeFinder, rewriter.exprGradeStore)
    newRewriter.formulaHintsStore = rewriter.formulaHintsStore
    newRewriter.config = rewriter.config
    newRewriter.recover(snapshot.rewriterSnapshot)
    newRewriter.solverContext = solver
    newRewriter.typeFinder.reset(snapshot.varTypes)
    rewriter = newRewriter
  }

  /**
   * Dispose the resources that are associated with the context: rewriter, solver, type finder.
   * The context should not be used after the call to dispose.
   */
  override def dispose(): Unit = {
    // dispose the rewriter, which will, in turn, dispose the solver
    rewriter.dispose()
    // nothing to dispose in the type finder
  }
}
