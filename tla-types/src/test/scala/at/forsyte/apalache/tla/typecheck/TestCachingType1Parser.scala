package at.forsyte.apalache.tla.typecheck

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCachingType1Parser  extends FunSuite {
  test("Int") {
    val parser = TypeParserFactory.cachingType1Parser()
    val result = parser("Int")
    assert(IntT1() == result)
  }
}