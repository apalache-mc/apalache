package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestArenaWithArraysFun extends TestArena {
  override protected def withFixture(test: NoArgTest): Outcome = {
    solver = new Z3SolverContext(SolverConfig.default.copy(debug = true, smtEncoding = arraysFunEncoding))
    val result = test()
    solver.dispose()
    result
  }
}
