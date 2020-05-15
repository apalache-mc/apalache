package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.FunSuite

@RunWith(classOf[JUnitRunner])
class TestJsonReader extends FunSuite {

  // compare expression and expected result (single-line formatting)
  def compare(expected: TlaEx, json: String): Unit = {
    assert(JsonReader.read(json) == expected)
  }

  test("str") {
    // "Hello, World!"
    compare(
      str("Hello, World!"),
      """{"str":"Hello, World!"}"""
    )
  }
}
