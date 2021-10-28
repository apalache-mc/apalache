package at.forsyte.apalache.tla.bmcmt.smt

import org.scalatest.Outcome

class TestRecordingSolverContextWithOOPSLA19 extends TestRecordingSolverContext {
  override protected def withFixture(test: OneArgTest): Outcome = {
    solverConfig = SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = oopsla19EncodingType)
    test()
  }
}
