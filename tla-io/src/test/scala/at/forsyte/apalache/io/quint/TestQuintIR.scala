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

  test("Invalid JSON returns sensible error") {
    QuintOutput.read("""{"foo": 1}""") match {
      case Success(_) => fail("should return a failure")
      case Failure(err) =>
        assert(err.getMessage().contains("missing keys in dictionary: stage, modules, types"))
    }
  }
}
