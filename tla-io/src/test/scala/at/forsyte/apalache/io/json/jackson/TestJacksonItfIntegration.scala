package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.itf.ItfJsonToTla
import at.forsyte.apalache.tla.types.tla
import com.fasterxml.jackson.databind.ObjectMapper
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

/**
 * Test showing how to use Jackson JsonNode with ItfJsonToTla.
 *
 * This demonstrates that you can now use Jackson instead of UJson for parsing ITF traces.
 */
@RunWith(classOf[JUnitRunner])
class TestJacksonItfIntegration extends AnyFunSuite {

  test("parse ITF trace from Jackson JSON string") {
    val itfParser = new ItfJsonToTla(JacksonScalaFromJsonAdapter)

    val itfJson = """{
      "#meta": {
        "format-description": "Example ITF trace",
        "varTypes": {
          "x": "Int",
          "y": "Str"
        }
      },
      "vars": ["x", "y"],
      "states": [
        {
          "x": 1,
          "y": "hello"
        },
        {
          "x": 2,
          "y": "world"
        }
      ]
    }"""

    val mapper = new ObjectMapper()
    val jsonNode = mapper.readTree(itfJson)
    val jacksonRep = JacksonRep(jsonNode)

    val result = itfParser.parseTrace(jacksonRep)

    assert(result.isRight, "expected successful parsing of ITF trace")
    val trace = result.toOption.get
    assert(trace.length == 2, "expected trace with 2 states")

    val state0 = trace(0)
    assert(state0("x") == tla.int(1).build, "expected x=1 in state 0")
    assert(state0("y") == tla.str("hello").build, "expected y='hello' in state 0")

    val state1 = trace(1)
    assert(state1("x") == tla.int(2).build, "expected x=2 in state 1")
    assert(state1("y") == tla.str("world").build, "expected y='world' in state 1")
  }

  test("create ITF trace programmatically using Jackson") {
    val itfParser = new ItfJsonToTla(JacksonScalaFromJsonAdapter)

    val meta = JacksonScalaToJsonAdapter.mkObj(
      "format-description" -> JacksonScalaToJsonAdapter.fromStr("Example ITF trace"),
      "varTypes" -> JacksonScalaToJsonAdapter.mkObj(
        "x" -> JacksonScalaToJsonAdapter.fromStr("Int"),
        "y" -> JacksonScalaToJsonAdapter.fromStr("Str")
      )
    )

    val vars = JacksonScalaToJsonAdapter.fromIterable(Seq(
      JacksonScalaToJsonAdapter.fromStr("x"),
      JacksonScalaToJsonAdapter.fromStr("y")
    ))

    val state1 = JacksonScalaToJsonAdapter.mkObj(
      "x" -> JacksonScalaToJsonAdapter.fromInt(1),
      "y" -> JacksonScalaToJsonAdapter.fromStr("hello")
    )

    val state2 = JacksonScalaToJsonAdapter.mkObj(
      "x" -> JacksonScalaToJsonAdapter.fromInt(2),
      "y" -> JacksonScalaToJsonAdapter.fromStr("world")
    )

    val states = JacksonScalaToJsonAdapter.fromIterable(Seq(state1, state2))

    val itfTrace = JacksonScalaToJsonAdapter.mkObj(
      "#meta" -> meta,
      "vars" -> vars,
      "states" -> states
    )

    val result = itfParser.parseTrace(itfTrace)

    assert(result.isRight, "expected successful parsing of programmatically created ITF trace")
    val trace = result.toOption.get
    assert(trace.length == 2, "expected trace with 2 states")

    val traceState0 = trace(0)
    assert(traceState0("x") == tla.int(1).build, "expected x=1 in state 0")
    assert(traceState0("y") == tla.str("hello").build, "expected y='hello' in state 0")

    val traceState1 = trace(1)
    assert(traceState1("x") == tla.int(2).build, "expected x=2 in state 1")
    assert(traceState1("y") == tla.str("world").build, "expected y='world' in state 1")
  }
}

