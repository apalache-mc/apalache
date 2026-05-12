package at.forsyte.apalache.io.itf

import at.forsyte.apalache.io.json.jackson.{JacksonRepresentation, ScalaFromJacksonAdapter, ScalaToJacksonAdapter}
import at.forsyte.apalache.io.json.ujsonimpl.{ScalaToUJsonAdapter, UJsonRepresentation}
import at.forsyte.apalache.io.lir.Trace
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestTlaToItfJson extends AnyFunSuite {
  private val ujsonEncoder = new TlaToItfJson[UJsonRepresentation](ScalaToUJsonAdapter)
  private val jacksonEncoder = new TlaToItfJson[JacksonRepresentation](ScalaToJacksonAdapter)

  test("UJson encoder emits ITF trace") {
    val intTag = Typed(IntT1)
    val module = TlaModule("test", List(TlaVarDecl("x")(intTag)))
    val trace = IndexedSeq[Trace.State](
        SortedMap(),
        SortedMap("x" -> tla.int(1).build),
        SortedMap("x" -> tla.int(2).build),
    )

    val actualJson = ujsonEncoder.mkJson(module, trace).value
    val expectedJson = ujson.read("""{
      "#meta": {
        "format": "ITF",
        "format-description": "https://apalache-mc.org/docs/adr/015adr-trace.html",
        "varTypes": { "x": "Int" }
      },
      "vars": [ "x" ],
      "states": [
        { "#meta": { "index": 0 }, "x": { "#bigint": "1" } },
        { "#meta": { "index": 1 }, "x": { "#bigint": "2" } }
      ]
    }""")

    assert(actualJson("#meta")("format") == expectedJson("#meta")("format"))
    assert(actualJson("#meta")("format-description") == expectedJson("#meta")("format-description"))
    assert(actualJson("#meta")("varTypes") == expectedJson("#meta")("varTypes"))
    assert(actualJson("vars") == expectedJson("vars"))
    assert(actualJson("states") == expectedJson("states"))
  }

  test("Jackson encoder emits parseable ITF trace") {
    val intTag = Typed(IntT1)
    val module = TlaModule("test", List(TlaVarDecl("x")(intTag)))
    val trace = IndexedSeq[Trace.State](
        SortedMap(),
        SortedMap("x" -> tla.int(1).build),
        SortedMap("x" -> tla.int(2).build),
    )

    val json = jacksonEncoder.mkJson(module, trace)
    val parsed = new ItfJsonToTla(ScalaFromJacksonAdapter).parseTrace(json)

    assert(parsed.contains(IndexedSeq(
                SortedMap("x" -> tla.int(1).build),
                SortedMap("x" -> tla.int(2).build),
            )))
  }
}
