package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.infra.passes.options.{SMTEncoding, SMTSolver}
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithOfflineAndCvc5FunArrays
    extends TestTransitionExecutorImpl[OfflineExecutionContextSnapshot] {
  override def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext.create(None,
        SolverConfig.default.copy(
            debug = false,
            smtEncoding = SMTEncoding.FunArrays,
            smtSolver = SMTSolver.CVC5,
            z3StatsSec = 0,
        ))
    withFixtureInContext(solver, new OfflineExecutionContext(_, new IncrementalRenaming(new IdleTracker)), test)
  }
}
