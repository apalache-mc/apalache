package at.forsyte.apalache.tla.bmcmt

import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

// TODO: Gradually substitute RewriterBase for concrete tests, as development in the "arrays" encoding progresses

@RunWith(classOf[JUnitRunner])
class TestRewriterWithArrays extends RewriterBase {
  override protected def withFixture(test: OneArgTest): Outcome = {
    test("arrays")
  }
}
