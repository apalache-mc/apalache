package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

/**
 * Test encodings against each other.
 *
 * @see
 *   [[CrossTestEncodings]]
 */
@RunWith(classOf[JUnitRunner])
class CrossTestEncodingsWithOOPSLA19VsArrays extends CrossTestEncodings {
  override def withFixture(test: NoArgTest): Outcome = {
    oracleEncoding = SMTEncoding.Oopsla19
    verifierEncoding = SMTEncoding.Arrays
    test()
  }
}
