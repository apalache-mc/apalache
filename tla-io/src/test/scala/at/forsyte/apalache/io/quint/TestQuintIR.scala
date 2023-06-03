package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import scala.util.Success
import scala.util.Failure

@RunWith(classOf[JUnitRunner])
class TestQuintIR extends AnyFunSuite {

  // tictactoe.json is located in tla-io/src/test/resources/tictactoe.json
  test("Can load tictactoe.json") {
    val tictactoeQuintJson = scala.io.Source.fromResource("tictactoe.json").mkString
    val quintIR = QuintOutput.read(tictactoeQuintJson).get
    assert(quintIR.modules(0).name == "tictactoe")
  }

  // clockSync3.json is located in tla-io/src/test/resources/clockSync3.json
  // Regression tests for https://github.com/informalsystems/quint/issues/927
  // and related serialization problems.
  test("Can load clockSync3.json") {
    val clockSync3QuintJson = scala.io.Source.fromResource("clockSync3.json").mkString
    val quintIR = QuintOutput.read(clockSync3QuintJson).get
    assert(quintIR.modules(0).name == "ClockSync3")
  }

  test("Invalid JSON returns sensible error") {
    QuintOutput.read("""{"foo": 1}""") match {
      case Success(_) => fail("should return a failure")
      case Failure(err) =>
        assert(err.getMessage().contains("missing keys in dictionary: stage, modules, types"))
    }
  }
}
