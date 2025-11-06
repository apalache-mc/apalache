package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.json.JsonDeserializationError
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestJacksonAdapters extends AnyFunSuite {

  test("JacksonScalaToJsonAdapter creates objects") {
    val obj = JacksonScalaToJsonAdapter.mkObj(
      "name" -> JacksonScalaToJsonAdapter.fromStr("Alice"),
      "age" -> JacksonScalaToJsonAdapter.fromInt(30),
      "active" -> JacksonScalaToJsonAdapter.fromBool(true)
    )

    assert(obj.value.isObject, "expected object node")
    assert(obj.allFieldsOpt.contains(Set("name", "age", "active")), "expected all fields present")
  }

  test("JacksonScalaToJsonAdapter creates arrays") {
    val arr = JacksonScalaToJsonAdapter.fromIterable(Seq(
      JacksonScalaToJsonAdapter.fromInt(1),
      JacksonScalaToJsonAdapter.fromInt(2),
      JacksonScalaToJsonAdapter.fromInt(3)
    ))

    assert(arr.value.isArray, "expected array node")
  }

  test("JacksonScalaFromJsonAdapter extracts integers") {
    val json = JacksonScalaToJsonAdapter.fromInt(42)
    assert(JacksonScalaFromJsonAdapter.asInt(json) == 42, "expected integer value 42")
  }

  test("JacksonScalaFromJsonAdapter extracts strings") {
    val json = JacksonScalaToJsonAdapter.fromStr("hello")
    assert(JacksonScalaFromJsonAdapter.asStr(json) == "hello", "expected string value 'hello'")
  }

  test("JacksonScalaFromJsonAdapter extracts booleans") {
    val json = JacksonScalaToJsonAdapter.fromBool(true)
    assert(JacksonScalaFromJsonAdapter.asBool(json), "expected boolean value true")
  }

  test("JacksonScalaFromJsonAdapter extracts arrays") {
    val json = JacksonScalaToJsonAdapter.fromIterable(Seq(
      JacksonScalaToJsonAdapter.fromInt(1),
      JacksonScalaToJsonAdapter.fromInt(2)
    ))
    val seq = JacksonScalaFromJsonAdapter.asSeq(json)
    assert(seq.length == 2, "expected sequence of length 2")
  }

  test("JacksonScalaFromJsonAdapter throws error on type mismatch") {
    val json = JacksonScalaToJsonAdapter.fromStr("not an int")
    assertThrows[JsonDeserializationError] {
      JacksonScalaFromJsonAdapter.asInt(json)
    }
  }

  test("JacksonRep getFieldOpt works correctly") {
    val obj = JacksonScalaToJsonAdapter.mkObj(
      "x" -> JacksonScalaToJsonAdapter.fromInt(10)
    )

    assert(obj.getFieldOpt("x").isDefined, "expected field 'x' to be present")
    assert(obj.getFieldOpt("y").isEmpty, "expected field 'y' to be absent")
  }
}

