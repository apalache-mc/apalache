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
class CrossTestEncodingsWithArraysVsOOPSLA19 extends CrossTestEncodings {
  override def withFixture(test: NoArgTest): Outcome = {
    oracleEncoding = arraysEncoding
    verifierEncoding = oopsla19Encoding
    test()
  }
}
