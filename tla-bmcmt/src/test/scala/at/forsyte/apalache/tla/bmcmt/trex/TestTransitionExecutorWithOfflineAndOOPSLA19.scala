package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.io.OutputWorkspaceMock
import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

/**
 * The tests for TransitionExecutorImpl that are using IncrementalSnapshot.
 *
 * @author
 *   Igor Konnov, Shon Feder
 */
@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithOfflineAndOOPSLA19 extends TestTransitionExecutorImpl[OfflineExecutionContextSnapshot] {
  override def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext
      .create(None,
          SolverConfig(
              debug = false,
              profile = false,
              randomSeed = 0,
              z3StatsSec = 0,
              smtEncoding = SMTEncoding.OOPSLA19,
          ), OutputWorkspaceMock)
    withFixtureInContext(solver,
        new OfflineExecutionContext(_, new IncrementalRenaming(new IdleTracker), OutputWorkspaceMock), test)
  }
}
