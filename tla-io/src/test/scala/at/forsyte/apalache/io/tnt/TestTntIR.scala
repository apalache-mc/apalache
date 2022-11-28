package at.forsyte.apalache.io.tnt

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import scala.util.Success
import scala.util.Failure

@RunWith(classOf[JUnitRunner])
class TestTntIR extends AnyFunSuite {

  // tictactoe.json is located in tla-io/src/test/resources/tictactoe.json
  test("Can load tictactoe.json") {
    val tictactoeTntJson = scala.io.Source.fromResource("tictactoe.json").mkString
    val tntIR = TntcOutput.read(tictactoeTntJson).get
    assert(tntIR.module.name == "tictactoe")
  }

  test("Invalid JSON returns sensible error") {
    TntcOutput.read("""{"foo": 1}""") match {
      case Success(_) => fail("should return a failure")
      case Failure(err) =>
        assert(err.getMessage().contains("missing keys in dictionary: status, module, types"))
    }
  }
}
