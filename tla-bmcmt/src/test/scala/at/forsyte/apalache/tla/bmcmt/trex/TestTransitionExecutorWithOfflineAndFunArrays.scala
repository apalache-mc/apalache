package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.io.OutputWorkspaceMock
import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithOfflineAndFunArrays
    extends TestTransitionExecutorImpl[OfflineExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext
      .create(None,
          SolverConfig(
              debug = false,
              profile = false,
              randomSeed = 0,
              z3StatsSec = 0,
              smtEncoding = SMTEncoding.FunArrays,
          ), OutputWorkspaceMock)
    withFixtureInContext(solver,
        new OfflineExecutionContext(_, new IncrementalRenaming(new IdleTracker), OutputWorkspaceMock), test)
  }
}
