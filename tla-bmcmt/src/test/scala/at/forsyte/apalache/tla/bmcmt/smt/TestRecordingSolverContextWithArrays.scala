package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRecordingSolverContextWithArrays extends TestRecordingSolverContext {
  override protected def withFixture(test: NoArgTest): Outcome = {
    solverConfig = SolverConfig(debug = false, profile = false, randomSeed = 0, z3StatsSec = 0,
        smtEncoding = SMTEncoding.Arrays)
    test()
  }
}
