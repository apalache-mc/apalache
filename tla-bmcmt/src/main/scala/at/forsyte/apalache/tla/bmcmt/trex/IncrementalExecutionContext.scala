package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter

/**
  * An executor context for an incremental SMT solver.
  *
  * @param rewriter an expression rewriter
  */
class IncrementalExecutionContext(val rewriter: SymbStateRewriter)
    extends ExecutionContext[IncrementalExecutionContextSnapshot] {

  /**
    * Create a snapshot of the context. This method is non-destructive, that is,
    * the context may be used after a snapshot has been made.
    *
    * @return a snapshot
    */
  override def snapshot(): IncrementalExecutionContextSnapshot = {
    val level = rewriter.contextLevel
    rewriter.push()
    IncrementalExecutionContextSnapshot(level, typeFinder.varTypes)
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
  override def recover(snapshot: IncrementalExecutionContextSnapshot): Unit = {
    val nPops = rewriter.contextLevel - snapshot.rewriterLevel
    if (nPops < 0) {
      throw new IllegalStateException(
        "Impossible to recover context to level %d from level %d"
          .format(snapshot.rewriterLevel, rewriter.contextLevel)
      )
    }

    rewriter.pop(nPops)
    rewriter.typeFinder.reset(snapshot.varTypes)
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
