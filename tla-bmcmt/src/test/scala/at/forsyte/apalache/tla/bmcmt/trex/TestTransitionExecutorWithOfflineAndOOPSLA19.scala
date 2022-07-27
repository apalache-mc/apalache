package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.infra.passes.options.SMTEncoding
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
      .createZ3(None, SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = SMTEncoding.OOPSLA19))
    withFixtureInContext(solver, new OfflineExecutionContext(_, new IncrementalRenaming(new IdleTracker)), test)
  }
}
