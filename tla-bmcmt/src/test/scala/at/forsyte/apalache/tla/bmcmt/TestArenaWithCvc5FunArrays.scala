package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.{SMTEncoding, SMTSolver}
import at.forsyte.apalache.tla.bmcmt.smt.{Cvc5SolverContext, SolverConfig}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestArenaWithCvc5FunArrays extends TestArena {
  override protected def withFixture(test: NoArgTest): Outcome = {
    solver = new Cvc5SolverContext(SolverConfig.default.copy(debug = true, smtEncoding = SMTEncoding.FunArrays,
            smtSolver = SMTSolver.CVC5))
    val result = test()
    solver.dispose()
    result
  }
}
