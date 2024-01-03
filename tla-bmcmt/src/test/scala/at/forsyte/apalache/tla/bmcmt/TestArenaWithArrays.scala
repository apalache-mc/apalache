package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestArenaWithArrays extends TestArena {
  override protected def withFixture(test: NoArgTest): Outcome = {
    solver = new Z3SolverContext(SolverConfig.default.copy(debug = true, smtEncoding = SMTEncoding.Arrays))
    val result = test()
    solver.dispose()
    result
  }
}
