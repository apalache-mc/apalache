package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import java.io.{PrintWriter, StringWriter}
import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestItfCounterexampleWriter extends AnyFunSuite {

  /**
   * Write a counterexample and compare the output to the expected result.
   *
   * @param rootModule
   *   the module that produced the counterexample
   * @param states
   *   a list of states: state 0 is the constant initializer, state 1 is the initial state, etc.
   * @param expected
   *   the expected output as a string
   */
  def compareJson(rootModule: TlaModule, states: List[NextState], expected: String): Unit = {
    val writer = new ItfCounterexampleWriter(new PrintWriter(new StringWriter()))
    val actualJson = writer.mkJson(rootModule, states)
    // erase the date from the description as it is time dependent
    actualJson("#meta")("description") = "Created by Apalache"
    val expectedJson = ujson.read(expected)
    assertResult(expectedJson)(actualJson)
  }

  test("ITF JSON no state") {
    val intTag = Typed(IntT1)
    compareJson(
        TlaModule("test", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag))),
        List(
            ("0", SortedMap("N" -> ValEx(TlaInt(4))(intTag)))
        ),
        """{
          |  "#meta": {
          |    "format": "ITF",
          |    "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
          |    "description": "Created by Apalache"
          |  },
          |  "params": [ "N" ],
          |  "vars": [ "x" ],
          |  "states": [
          |    {
          |      "#meta": {
          |        "index": 0
          |      },
          |      "N": 4
          |    }
          |  ]
          |}""".stripMargin,
    )
  }

  test("ITF JSON single state") {
    val intSeq = SeqT1(IntT1)
    val intAndStr = TupT1(IntT1, StrT1)
    val intSetT = SetT1(IntT1)
    val fooBar = RecT1("foo" -> IntT1, "bar" -> BoolT1)
    val intToStr = FunT1(IntT1, StrT1)
    val boolToInt = FunT1(BoolT1, IntT1)

    def pair(i: Int, s: String) = tuple(int(i), str(s)).as(intAndStr)
    val decls = List(
        TlaVarDecl("a")(Typed(IntT1)),
        TlaVarDecl("b")(Typed(StrT1)),
        TlaVarDecl("c")(Typed(intSeq)),
        TlaVarDecl("d")(Typed(intSetT)),
        TlaVarDecl("e")(Typed(fooBar)),
        TlaVarDecl("f")(Typed(intAndStr)),
        TlaVarDecl("g")(Typed(intToStr)),
        TlaVarDecl("h")(Typed(intToStr)),
    )

    compareJson(
        TlaModule("test", decls),
        List(
            ("A", SortedMap()),
            ("B",
                SortedMap(
                    // 2
                    "a" -> int(2).as(IntT1),
                    // "hello"
                    "b" -> str("hello").as(StrT1),
                    // 1000000000000000000 > 2^53 - 1
                    "c" -> tuple(int(3), int(BigInt("1000000000000000000", 10))).as(intSeq),
                    // { 5, 6 }
                    "d" -> enumSet(int(5), int(6))
                      .as(intSetT),
                    // [ foo |-> 3, bar |-> TRUE ]
                    "e" -> enumFun(str("foo"), int(3), str("bar"), bool(true))
                      .as(fooBar),
                    // <<7, "myStr">>
                    "f" -> tuple(int(7), str("myStr"))
                      .as(intAndStr),
                    // SetAsFun({ <<1, "a">>, <<2, "b">>, <<3, "c">> })
                    "g" -> (apalacheSetAsFun(enumSet(pair(1, "a"), pair(2, "b"), pair(3, "c"))
                              .as(SetT1(intAndStr))).as(intToStr)),
                    // SetAsFun({})
                    "h" -> (apalacheSetAsFun(enumSet().as(SetT1(intAndStr))).as(intToStr)),
                    // SetAsFun({ <<1, "a">> })
                    "i" -> (apalacheSetAsFun(enumSet(pair(1, "a")).as(SetT1(intAndStr))).as(intToStr)),
                    // [ BOOLEAN -> Int ]
                    "j" -> funSet(booleanSet(), intSet()).as(SetT1(boolToInt)),
                    // SUBSET BOOLEAN
                    "k" -> powSet(booleanSet()).as(SetT1(BoolT1)),
                    // Int
                    "l" -> intSet().as(intSetT),
                    // Nat
                    "m" -> natSet().as(intSetT),
                )),
        ),
        """{
          |  "#meta": {
          |    "format": "ITF",
          |    "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
          |    "description": "Created by Apalache"
          |  },
          |  "vars": [ "a", "b", "c", "d", "e", "f", "g", "h" ],
          |  "states": [
          |    {
          |      "#meta": { "index": 0 },
          |      "a": 2,
          |      "b": "hello",
          |      "c": [ 3, { "#bigint": "1000000000000000000" } ],
          |      "d": { "#set": [ 5, 6 ] },
          |      "e": { "foo": 3, "bar": true },
          |      "f": { "#tup": [ 7, "myStr" ] },
          |      "g": { "#map": [[1, "a"], [2, "b"], [3, "c"]] },
          |      "h": { "#map": [] },
          |      "i": { "#map": [[1, "a"]] },
          |      "j": { "#unserializable": "[BOOLEAN → Int]" },
          |      "k": { "#unserializable": "SUBSET BOOLEAN" },
          |      "l": { "#unserializable": "Int" },
          |      "m": { "#unserializable": "Nat" }
          |    }
          |  ]
          |}""".stripMargin,
    )
  }
}
