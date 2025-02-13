package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithIncrementalAndFunArrays
    extends TestTransitionExecutorImpl[IncrementalExecutionContextSnapshot]
    with TestFilteredTransitionExecutor[IncrementalExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = new Z3SolverContext(SolverConfig(
            debug = false,
            profile = false,
            randomSeed = 0,
            z3StatsSec = 0,
            smtEncoding = SMTEncoding.FunArrays,
        ))
    withFixtureInContext(solver, new IncrementalExecutionContext(_), test)
  }
}
