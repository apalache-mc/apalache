package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.io.OutputWorkspaceMock
import at.forsyte.apalache.io.config.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
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
class TestTransitionExecutorWithIncrementalAndOOPSLA19
    extends TestTransitionExecutorImpl[IncrementalExecutionContextSnapshot]
    with TestFilteredTransitionExecutor[IncrementalExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver =
      new Z3SolverContext(SolverConfig(
              debug = false,
              profile = false,
              randomSeed = 0,
              z3StatsSec = 0,
              smtEncoding = SMTEncoding.OOPSLA19,
          ), OutputWorkspaceMock)
    withFixtureInContext(solver, new IncrementalExecutionContext(_), test)
  }
}
