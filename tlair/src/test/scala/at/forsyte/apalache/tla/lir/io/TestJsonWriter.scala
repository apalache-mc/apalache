package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.predef.TlaRealSet
import at.forsyte.apalache.tla.lir.{OperEx, SimpleFormalParam, TlaEx, TlaOperDecl, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

@RunWith(classOf[JUnitRunner])
class TestJsonWriter extends FunSuite with BeforeAndAfterEach {

  // compare expression and expected result (single-line formatting)
  def compare(ex: TlaEx, expected: String, indent: Int = -1): Unit = {
    val stringWriter = new StringWriter()
    val printWriter = new PrintWriter(stringWriter)
    val writer = new JsonWriter(printWriter, indent)
    writer.write(ex)
    printWriter.flush()
    assert(stringWriter.toString == expected)
  }

  // compare expression and expected result (multi-line formatting)
  def compareMultiLine(ex: TlaEx, expected: String): Unit =
    compare(ex, expected, 2)

  test("id") {
    // awesome
    compare(
      name("awesome"),
      """"awesome""""
    )
  }

  test("str") {
    // "Hello, World!"
    compare(
      str("Hello, World!"),
      """{"str":"Hello, World!"}"""
    )
  }

  test("int") {
    // int
    compare(
      int(42),
      """{"int":"42"}"""
    )
  }

  test("RealSet") {
    // Real
    compare(
      ValEx(TlaRealSet), // TODO: builders for sets? (Andrey)
      """{"set":"Real"}"""
    )
  }

  test("prime name") {
    // awesome'
    compare(
      prime("awesome"),
      """{"prime":"awesome"}"""
    )
  }

  test("empty set") {
    // { }
    compare(
      enumSet(),
      """{"enum":[]}"""
    )
  }
  //
  test("singleton set") {
    // { 42 }
    compare(
      enumSet(42),
      """{"enum":[{"int":"42"}]}"""
    )
  }

  test("singleton set multi-line") {
    // { 42 }
    compareMultiLine(
      enumSet(42),
      """{
        |  "enum": [
        |    {
        |      "int": "42"
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("enum") {
    // { 1, 2, 3 }
    compare(
      enumSet(int(1), int(2), int(3)),
      """{"enum":[{"int":"1"},{"int":"2"},{"int":"3"}]}"""
    )
  }

  test("enum multi-line") {
    // { 1, 2, 3 }
    compareMultiLine(
      enumSet(int(1), int(2), int(3)),
      """{
        |  "enum": [
        |    {
        |      "int": "1"
        |    },
        |    {
        |      "int": "2"
        |    },
        |    {
        |      "int": "3"
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("tuple") {
    // << 1, two, "three" >>
    compare(
      tuple(int(1), name("two"), str("three")),
      """{"tuple":[{"int":"1"},"two",{"str":"three"}]}"""
    )
  }

  test("conjunction") {
    // a /\ b /\ c
    compare(
      and(name("a"), name("b"), name("c")),
      """{"and":["a","b","c"]}"""
    )
  }

  test("minus") {
    // 1 - 2
    compare(
      minus(int(1), int(2)),
      """{"-":[{"int":"1"},{"int":"2"}]}"""
    )
  }

  test("function definition") {
    // [ x \in S, y \in T |-> x + y ]
    compareMultiLine(
      funDef(plus("x", "y"), "x", "S", "y", "T"),
      """{
        |  "function": {
        |    "+": [
        |      "x",
        |      "y"
        |    ]
        |  },
        |  "where": [
        |    "x",
        |    "S",
        |    "y",
        |    "T"
        |  ]
        |}""".stripMargin
    )
  }

  test("function application") {
    // f[e]
    compare(
      appFun("f", "e"),
      """{"apply":"f","to":"e"}"""
    )
  }

  test("double function application") {
    // f[e][g]
    compare(
      appFun(appFun("f", "e"), "g"),
      """{"apply":{"apply":"f","to":"e"},"to":"g"}"""
    )
  }

  test("function except") {
    // [f EXCEPT ![k] = v]
    compare(
      except("f", "k", "v"),
      """{"except":"f","where":["k","v"]}"""
    )
  }

  test("record / function enumeration") {
    // [ k_1 |-> v_1, ..., k_n |-> v_n ]
    compare(
      enumFun(
        str("x1"), "y1",
        str("x2"), "y2",
        str("x3"), "y3"
      ),
      """{"record":[{"str":"x1"},"y1",{"str":"x2"},"y2",{"str":"x3"},"y3"]}"""
    )
  }

  test("function set") {
    // [S -> T]
    compare(
      funSet(name("S"), name("T")),
      """{"function-set":["S","T"]}"""
    )
  }

  test("record set") {
    // [x: S -> T]
    compare(
      recSet(
        str("x"), "S",
        str("y"), "T",
        str("z"), "U"
      ),
      """{"record-set":[{"str":"x"},"S",{"str":"y"},"T",{"str":"z"},"U"]}"""
    )
  }

  test("filter") {
    // {x \in S: P}
    compare(
      filter("x", "S", "P"),
      """{"filter":["x","S"],"that":"P"}"""
    )
  }

  test("filter with predicate") {
    // {x \in S: P}
    compareMultiLine(
      filter("x", "S", lt("x", 5)),
      """{
        |  "filter": [
        |    "x",
        |    "S"
        |  ],
        |  "that": {
        |    "<": [
        |      "x",
        |      {
        |        "int": "5"
        |      }
        |    ]
        |  }
        |}""".stripMargin
    )
  }

  test("map") {
    // {x+y: x \in S, y \in T}
    compare(
      map(plus("x", "y"), "x", "S", "y", "T"),
      """{"map":{"+":["x","y"]},"where":["x","S","y","T"]}"""
    )
  }

  test("exists bounded") {
    // \E x \in S : P
    compare(
      exists("x", "S", "P"),
      """{"exists":["x","S"],"that":"P"}"""
    )
  }

  test("exists unbounded") {
    // \E x : P
    compare(
      exists("x", "P"),
      """{"exists":"x","that":"P"}"""
    )
  }

  test("choose bounded") {
    // CHOOSE x \in S : x > 3
    compare(
      choose("x", "S", gt("x",3)),
      """{"CHOOSE":["x","S"],"that":{">":["x",{"int":"3"}]}}"""
    )
  }

  test("choose unbounded") {
    // CHOOSE <<x, y>> : x + y <= 5
    compareMultiLine(
      choose(tuple("x", "y"), le(plus("x","y"),5)),
      """{
        |  "CHOOSE": {
        |    "tuple": [
        |      "x",
        |      "y"
        |    ]
        |  },
        |  "that": {
        |    "<=": [
        |      {
        |        "+": [
        |          "x",
        |          "y"
        |        ]
        |      },
        |      {
        |        "int": "5"
        |      }
        |    ]
        |  }
        |}""".stripMargin
    )
  }

  test("if then else") {
    // \E x \in S : P
    compare(
      ite("p", "x", "y"),
      """{"IF":"p","THEN":"x","ELSE":"y"}"""
    )
  }

  test("case split") {
    // CASE guard1 -> action1
    //   [] guard2 -> action2
    compare(
      caseSplit("guard1", "action1", "guard2", "action2"),
      """{"CASE":["guard1","action1","guard2","action2"]}"""
    )
  }

  test("case with other") {
    // CASE guard1 -> action1
    //   [] guard2 -> action2
    //   [] OTHER -> otherAction
    compare(
      caseOther("otherAction", "guard1", "action1", "guard2", "action2"),
      """{"CASE":["guard1","action1","guard2","action2"],"OTHER":"otherAction"}"""
    )
  }

  test("[A]_x") {
    // [A]_x
    compare(
      stutt("A", "x"),
      """{"stutter":"A","vars":"x"}"""
    )
  }

  test("<A>_<<x,y>>") {
    // <A>_vars
    compare(
      nostutt("A", tuple("x", "y")),
      """{"nostutter":"A","vars":{"tuple":["x","y"]}}"""
    )
  }

  test("WF_x(A)") {
    // [A]_x
    compare(
      WF("x", "A"),
      """{"WF":"A","vars":"x"}"""
    )
  }

  test("SF_<<x,y>>(A)") {
    // <A>_vars
    compare(
      SF(tuple("x", "y"), "A"),
      """{"SF":"A","vars":{"tuple":["x","y"]}}"""
    )
  }

  test("L2 :: 1") {
    // <A>_vars
    compare(
      label(int(1), "L2"),
      """{"int":"1","label":{"name":"L2","args":[]}}"""
    )
  }

  test("L2(a, b) :: f(x+y)>2") {
    // <A>_vars
    compare(
      label(appFun("f", gt(plus("x","y"),2)), "L2", "a", "b"),
      """{"apply":"f","to":{">":[{"+":["x","y"]},{"int":"2"}]},"label":{"name":"L2","args":["a","b"]}}"""
    )
  }
}
