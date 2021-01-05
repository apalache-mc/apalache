package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.transformations.{PredResult, PredResultFail, PredResultOk}
import org.scalatest.FunSuite

/**
  * A trait that is useful for testing of language predicates.
  */
class LanguagePredTestSuite extends FunSuite {
  def expectOk(result: PredResult): Unit = {
    result match {
      case PredResultOk() => ()
      case _ => fail("Expected PredResultOk, found: " + result)
    }
  }

  def expectFail(result: PredResult): Unit = {
    result match {
      case PredResultFail(_) => ()
      case _ => fail("Expected PredResultFail(_), found: " + result)
    }
  }
}
