package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import ujson.Value

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestItfTraceWriter extends AnyFunSuite {

  /**
   * Write a counterexample to compare the output to the expected result.
   *
   * @param rootModule
   *   the module that produced the counterexample
   * @param states
   *   a list of states: state 0 is the constant initializer, state 1 is the initial state, etc.
   */
  def mkJson(rootModule: TlaModule, states: IndexedSeq[Trace.State]): Value =
    ItfCounterexampleWriter.mkJson(rootModule, states)


  test("ITF JSON no state") {
    val intTag = Typed(IntT1)
    val actualJson = mkJson(
        TlaModule("test", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag))),
        IndexedSeq(SortedMap("N" -> tla.int(4).build)),
    )
    val rawExpected =
      s"""{
        |  "#meta": {
        |    "format": "ITF",
        |    "format-description": "https://apalache-mc.org/docs/adr/015adr-trace.html",
        |    "description": "Created by Apalache"
        |  },
        |  "params": [ "N" ],
        |  "vars": [ "x" ],
        |  "states": [
        |    {
        |      "#meta": {
        |        "index": 0
        |      },
        |      "N": { "#bigint": "4" }
        |    }
        |  ]
        |}""".stripMargin

    val expectedJson = ujson.read(rawExpected)

    assert(actualJson("params") == expectedJson("params"))
    assert(actualJson("vars") == expectedJson("vars"))
    assert(actualJson("states") == expectedJson("states"))
    assert(actualJson("#meta")("format") == expectedJson("#meta")("format"))
    assert(actualJson("#meta")("format-description") == expectedJson("#meta")("format-description"))
  }

  test("ITF JSON single state") {
    val intSeq = SeqT1(IntT1)
    val intAndStr = TupT1(IntT1, StrT1)
    val intSetT = SetT1(IntT1)
    val fooBar = RecT1("foo" -> IntT1, "bar" -> BoolT1)
    val intToStr = FunT1(IntT1, StrT1)
//    val fooBarRow = RecRowT1(RowT1("foo" -> IntT1, "bar" -> BoolT1))
    val variantT = VariantT1(RowT1("Baz" -> fooBar, "Boo" -> IntT1))

    import tla._

    def pair(i: Int, s: String) = tuple(int(i), str(s))

    val decls = List(
        TlaVarDecl("a")(Typed(IntT1)),
        TlaVarDecl("b")(Typed(StrT1)),
        TlaVarDecl("c")(Typed(intSeq)),
        TlaVarDecl("d")(Typed(intSetT)),
        TlaVarDecl("e")(Typed(fooBar)),
        TlaVarDecl("f")(Typed(intAndStr)),
        TlaVarDecl("g")(Typed(intToStr)),
        TlaVarDecl("h")(Typed(intToStr)),
        TlaVarDecl("n")(Typed(variantT)),
    )

    val fooBarEx = recMixed(str("foo"), int(3), str("bar"), bool(true))

    val actualJson = mkJson(
        TlaModule("test", decls),
        IndexedSeq(
            SortedMap(),
            SortedMap[String, TlaEx](
                // 2
                "a" -> int(2),
                // "hello"
                "b" -> str("hello"),
                // 1000000000000000000 > 2^53 - 1
                "c" -> seq(int(3), int(BigInt("1000000000000000000", 10))),
                // { 5, 6 }
                "d" -> enumSet(int(5), int(6)),
                // [ foo |-> 3, bar |-> TRUE ]
                "e" -> fooBarEx,
                // <<7, "myStr">>
                "f" -> pair(7, "myStr"),
                // SetAsFun({ <<1, "a">>, <<2, "b">>, <<3, "c">> })
                "g" -> setAsFun(enumSet(pair(1, "a"), pair(2, "b"), pair(3, "c"))),
                // SetAsFun({})
                "h" -> setAsFun(emptySet(intAndStr)),
                // SetAsFun({ <<1, "a">> })
                "i" -> setAsFun(enumSet(pair(1, "a"))),
                // [ BOOLEAN -> Int ]
                "j" -> funSet(booleanSet(), intSet()),
                // SUBSET BOOLEAN
                "k" -> powSet(booleanSet()),
                // Int
                "l" -> intSet(),
                // Nat
                "m" -> natSet(),
                // Variant("Baz", [ foo |-> 3, bar |-> TRUE ])
                "n" -> variant("Baz", fooBarEx, variantT),
            ),
        ),
    )

    val rawExpected =
      """{
        |  "#meta": {
        |    "format": "ITF",
        |    "format-description": "https://apalache-mc.org/docs/adr/015adr-trace.html",
        |    "description": "Created by Apalache"
        |  },
        |  "vars": [ "a", "b", "c", "d", "e", "f", "g", "h", "n" ],
        |  "states": [
        |    {
        |      "#meta": { "index": 0 },
        |      "a": { "#bigint": "2" },
        |      "b": "hello",
        |      "c": [ { "#bigint": "3" }, { "#bigint": "1000000000000000000" } ],
        |      "d": { "#set": [ { "#bigint": "5" }, { "#bigint": "6" } ] },
        |      "e": { "foo": { "#bigint": "3" }, "bar": true },
        |      "f": { "#tup": [ { "#bigint": "7" }, "myStr" ] },
        |      "g": { "#map": [[{ "#bigint": "1" }, "a"], [{ "#bigint": "2" }, "b"], [{ "#bigint": "3" }, "c"]] },
        |      "h": { "#map": [] },
        |      "i": { "#map": [[{ "#bigint": "1" }, "a"]] },
        |      "j": { "#unserializable": "[BOOLEAN → Int]" },
        |      "k": { "#unserializable": "SUBSET BOOLEAN" },
        |      "l": { "#unserializable": "Int" },
        |      "m": { "#unserializable": "Nat" },
        |      "n": { "tag": "Baz", "value": { "foo": { "#bigint": "3" }, "bar": true }}
        |    }
        |  ]
        |}""".stripMargin

    val expectedJson = ujson.read(rawExpected)

    assert(actualJson("vars") == expectedJson("vars"))
    assert(actualJson("states") == expectedJson("states"))
    assert(actualJson("#meta")("format") == expectedJson("#meta")("format"))
    assert(actualJson("#meta")("format-description") == expectedJson("#meta")("format-description"))
  }
}
