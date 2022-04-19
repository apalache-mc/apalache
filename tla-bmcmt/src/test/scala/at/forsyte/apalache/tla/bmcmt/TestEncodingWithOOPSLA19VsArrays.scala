package at.forsyte.apalache.tla.bmcmt

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
    oracleEncoding = oopsla19Encoding
    verifierEncoding = arraysEncoding
    test()
  }
}
