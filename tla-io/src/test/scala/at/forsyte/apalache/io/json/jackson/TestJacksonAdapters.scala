package at.forsyte.apalache.io.json.jackson

import at.forsyte.apalache.io.json.JsonDeserializationError
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestJacksonAdapters extends AnyFunSuite {

  test("JacksonScalaToJsonAdapter creates objects") {
    val obj = ScalaToJacksonAdapter.mkObj(
      "name" -> ScalaToJacksonAdapter.fromStr("Alice"),
      "age" -> ScalaToJacksonAdapter.fromInt(30),
      "active" -> ScalaToJacksonAdapter.fromBool(true)
    )

    assert(obj.value.isObject, "expected object node")
    assert(obj.allFieldsOpt.contains(Set("name", "age", "active")), "expected all fields present")
  }

  test("JacksonScalaToJsonAdapter creates arrays") {
    val arr = ScalaToJacksonAdapter.fromIterable(Seq(
      ScalaToJacksonAdapter.fromInt(1),
      ScalaToJacksonAdapter.fromInt(2),
      ScalaToJacksonAdapter.fromInt(3)
    ))

    assert(arr.value.isArray, "expected array node")
  }

  test("JacksonScalaFromJsonAdapter extracts integers") {
    val json = ScalaToJacksonAdapter.fromInt(42)
    assert(ScalaFromJacksonAdapter.asInt(json) == 42, "expected integer value 42")
  }

  test("JacksonScalaFromJsonAdapter extracts strings") {
    val json = ScalaToJacksonAdapter.fromStr("hello")
    assert(ScalaFromJacksonAdapter.asStr(json) == "hello", "expected string value 'hello'")
  }

  test("JacksonScalaFromJsonAdapter extracts booleans") {
    val json = ScalaToJacksonAdapter.fromBool(true)
    assert(ScalaFromJacksonAdapter.asBool(json), "expected boolean value true")
  }

  test("JacksonScalaFromJsonAdapter extracts arrays") {
    val json = ScalaToJacksonAdapter.fromIterable(Seq(
      ScalaToJacksonAdapter.fromInt(1),
      ScalaToJacksonAdapter.fromInt(2)
    ))
    val seq = ScalaFromJacksonAdapter.asSeq(json)
    assert(seq.length == 2, "expected sequence of length 2")
  }

  test("JacksonScalaFromJsonAdapter throws error on type mismatch") {
    val json = ScalaToJacksonAdapter.fromStr("not an int")
    assertThrows[JsonDeserializationError] {
      ScalaFromJacksonAdapter.asInt(json)
    }
  }

  test("JacksonRep getFieldOpt works correctly") {
    val obj = ScalaToJacksonAdapter.mkObj(
      "x" -> ScalaToJacksonAdapter.fromInt(10)
    )

    assert(obj.getFieldOpt("x").isDefined, "expected field 'x' to be present")
    assert(obj.getFieldOpt("y").isEmpty, "expected field 'y' to be absent")
  }
}

