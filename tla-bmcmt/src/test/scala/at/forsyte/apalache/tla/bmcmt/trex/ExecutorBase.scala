package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.analyses.ExprGradeStoreImpl
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.SymbStateRewriterImpl
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming

import java.io.{File, FileOutputStream, PrintStream}
import org.scalatest.Outcome
import org.scalatest.funsuite.FixtureAnyFunSuite

trait ExecutorBase[SnapshotT] extends FixtureAnyFunSuite {
  type ExecutorContextT = ExecutionContext[SnapshotT]
  type FixtureParam = ExecutorContextT

  /**
   * Create a `withFixture` method using that works within execution context constructed from the `ctxFactory`, using
   * the given solver
   */
  protected def withFixtureInContext(
      solver: SolverContext,
      exeCtxFactory: SymbStateRewriterImpl => ExecutorContextT,
      test: OneArgTest): Outcome = {
    val rewriter = new SymbStateRewriterImpl(solver, new IncrementalRenaming(new IdleTracker), new ExprGradeStoreImpl())
    val exeCtx = exeCtxFactory(rewriter)

    // Tmp file to capture the noisy stdout from these tests
    // otherwise they pollute stdout on our CI making it hard to see failures
    val tmp = File.createTempFile("tla-bmcmt-test-output-", ".tmp")
    tmp.deleteOnExit()

    try {
      System.setOut(new PrintStream(new FileOutputStream(tmp)))
      test(exeCtx)
    } finally {
      exeCtx.dispose()
      System.setOut(System.out)
    }
  }

  protected def assertValid(trex: TransitionExecutorImpl[SnapshotT], assertion: TlaEx): Unit = {
    var snapshot = trex.snapshot()
    trex.assertState(assertion)
    assert(trex.sat(0).contains(true))
    trex.recover(snapshot)

    snapshot = trex.snapshot()
    trex.assertState(tla.not(assertion))
    assert(trex.sat(0).contains(false))
    trex.recover(snapshot)
  }
}
