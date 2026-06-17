package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.infra.passes.options.{SMTEncoding, SMTSolver}
import at.forsyte.apalache.tla.bmcmt.smt.{Cvc5SolverContext, SolverConfig}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithIncrementalAndCvc5OOPSLA19
    extends TestTransitionExecutorImpl[IncrementalExecutionContextSnapshot]
    with TestFilteredTransitionExecutor[IncrementalExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = new Cvc5SolverContext(SolverConfig.default.copy(
            debug = false,
            smtEncoding = SMTEncoding.OOPSLA19,
            smtSolver = SMTSolver.CVC5,
            z3StatsSec = 0,
        ))
    withFixtureInContext(solver, new IncrementalExecutionContext(_), test)
  }
}
