package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.tla.bmcmt.oopsla19Encoding
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRecordingSolverContextWithOOPSLA19 extends TestRecordingSolverContext {
  override protected def withFixture(test: OneArgTest): Outcome = {
    solverConfig = SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = oopsla19Encoding)
    test()
  }
}
