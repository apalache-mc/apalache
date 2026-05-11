package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.{SMTEncoding, SMTSolver}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRecordingSolverContextWithCvc5FunArrays extends TestRecordingSolverContext {
  override protected def withFixture(test: NoArgTest): Outcome = {
    solverConfig = SolverConfig.default
      .copy(smtEncoding = SMTEncoding.FunArrays, smtSolver = SMTSolver.CVC5, z3StatsSec = 0)
    test()
  }
}
