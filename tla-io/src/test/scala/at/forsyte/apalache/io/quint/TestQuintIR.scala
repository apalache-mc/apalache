package at.forsyte.apalache.io.quint

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.util.{Failure, Success}

@RunWith(classOf[JUnitRunner])
class TestQuintIR extends AnyFunSuite {

  test("Deserializes BigInt") {
    val someBigInt = "42" + Long.MaxValue.toString() + "42"

    // unquoted; tests `visitFloat64StringParts`
    assert(QuintDeserializer.read[BigInt]("0") == BigInt(0))
    assert(QuintDeserializer.read[BigInt]("1") == BigInt(1))
    assert(QuintDeserializer.read[BigInt]("-1") == BigInt(-1))
    assert(QuintDeserializer.read[BigInt](someBigInt) == BigInt(someBigInt))
    assert(QuintDeserializer.read[BigInt](s"-${someBigInt}") == BigInt("-" + someBigInt))

    // quoted; tests `visitString`
    assert(QuintDeserializer.read[BigInt]("\"0\"") == BigInt(0))
    assert(QuintDeserializer.read[BigInt]("\"1\"") == BigInt(1))
    assert(QuintDeserializer.read[BigInt]("\"-1\"") == BigInt(-1))
    assert(QuintDeserializer.read[BigInt](s"\"${someBigInt}\"") == BigInt(someBigInt))
    assert(QuintDeserializer.read[BigInt](s"\"-${someBigInt}\"") == BigInt("-" + someBigInt))
  }

  test("Serializes BigInt") {
    val someBigIntStr = "42" + Long.MaxValue.toString() + "42"

    assert(QuintDeserializer.write[BigInt](BigInt(0)) == "0")
    assert(QuintDeserializer.write[BigInt](BigInt(1)) == "1")
    assert(QuintDeserializer.write[BigInt](BigInt(-1)) == "-1")
    assert(QuintDeserializer.write[BigInt](BigInt(someBigIntStr)) == someBigIntStr)
    assert(QuintDeserializer.write[BigInt](BigInt(s"-${someBigIntStr}")) == s"-${someBigIntStr}")
  }

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
    assert(quintIR.modules(0).name == "clockSync3")
  }

  test("Invalid JSON returns sensible error") {
    QuintOutput.read("""{"foo": 1}""") match {
      case Success(_) => fail("should return a failure")
      case Failure(err) =>
        assert(err.getMessage().contains("missing keys in dictionary: stage, modules, types"))
    }
  }
}
