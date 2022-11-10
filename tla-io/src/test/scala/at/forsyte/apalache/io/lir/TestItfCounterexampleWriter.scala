package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import ujson.Value

import scala.collection.immutable.SortedMap

@RunWith(classOf[JUnitRunner])
class TestItfCounterexampleWriter extends AnyFunSuite {

  /**
   * Write a counterexample to compare the output to the expected result.
   *
   * @param rootModule
   *   the module that produced the counterexample
   * @param states
   *   a list of states: state 0 is the constant initializer, state 1 is the initial state, etc.
   */
  def mkJson(rootModule: TlaModule, states: List[NextState]): Value =
    ItfCounterexampleWriter.mkJson(rootModule, states)

  private class AbstractAccess
  sealed private case class ArrayAccess(i: Int) extends AbstractAccess {
    override def toString: Transition = i.toString
  }
  sealed private case class ObjectAccess(s: String) extends AbstractAccess {
    override def toString: Transition = s
  }

  import scala.language.implicitConversions

  implicit private def fromStr(s: String): AbstractAccess = ObjectAccess(s)

  // Attempts to access a ujson Value, by means of either an array-index or object-key.
  // Returns None when accessing a non-array by array index or a non-object by key, or if
  // the specified index/key does not exist.
  private def tryAccess(v: Value, access: AbstractAccess): Option[Value] = access match {
    case ArrayAccess(i)  => v.arrOpt.flatMap(arr => arr.lift(i))
    case ObjectAccess(s) => v.objOpt.flatMap(_.get(s))
  }

  /**
   * Asserts that P(seq)(json1,json2) holds for every seq in nesetedAccess, where P(seq)(json1,json2) is defined as
   *   - json1 = json2, if seq is empty, and
   *   - if seq = h +: t, a conjunction of:
   *     - json1 defines a field h, or list of length at least h
   *     - json2 defines a field h, or list of length at least h
   *     - P(t)(json1(h),json2(h)) or,
   *
   * In other words, for every sequence Seq(s1,...,sn) in nestedFields json1.s1.s2.(...).sn and json2.s1.s2.(...).sn
   * must be well defined and equal.
   */
  def assertEqualOver(nesetedAccess: Seq[AbstractAccess]*)(json1: Value, json2: Value): Unit = {
    def prop(seq: Seq[AbstractAccess])(v1: Value, v2: Value): Boolean = seq match {
      case Seq() => v1 == v2
      case h +: t =>
        (
            for {
              v1AtH <- tryAccess(v1, h)
              v2AtH <- tryAccess(v2, h)
            } yield prop(t)(v1AtH, v2AtH)
        ).getOrElse(false)
    }
    nesetedAccess.foreach { accessSeq =>
      assert(
          prop(accessSeq)(json1, json2),
          s": Inputs differ on _${accessSeq.map(a => s"(${a.toString})").mkString("")}",
      )
    }

  }

  test("ITF JSON no state") {
    val intTag = Typed(IntT1)
    val actualJson = mkJson(
        TlaModule("test", List(TlaConstDecl("N")(intTag), TlaVarDecl("x")(intTag))),
        List(("0", SortedMap("N" -> tla.int(4).build))),
    )
    val rawExpected =
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
        |}""".stripMargin

    val expectedJson = ujson.read(rawExpected)

    assertEqualOver(
        Seq("params"),
        Seq("vars"),
        Seq("states"),
        Seq("#meta", "format"),
        Seq("#meta", "format-description"),
    )(actualJson, expectedJson)

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
        List(
            ("A", SortedMap()),
            ("B",
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
                )),
        ),
    )

    val rawExpected =
      """{
        |  "#meta": {
        |    "format": "ITF",
        |    "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
        |    "description": "Created by Apalache"
        |  },
        |  "vars": [ "a", "b", "c", "d", "e", "f", "g", "h", "n" ],
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
        |      "m": { "#unserializable": "Nat" },
        |      "n": { "tag": "Baz", "value": { "foo": 3, "bar": true }}
        |    }
        |  ]
        |}""".stripMargin

    val expectedJson = ujson.read(rawExpected)

    assertEqualOver(
        Seq("vars"),
        Seq("states"),
        Seq("#meta", "format"),
        Seq("#meta", "format-description"),
    )(actualJson, expectedJson)

  }
}
