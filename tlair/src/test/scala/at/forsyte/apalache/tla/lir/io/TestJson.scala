package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import at.forsyte.apalache.tla.lir.values._
import upickle._

import scala.collection.immutable.HashMap
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
 * <p>Geeneric set of tests for conversion between TLA and JSON.</p>
 * @author Andrey Kuprianov
 **/

@RunWith(classOf[JUnitRunner])
abstract class TestJson extends FunSuite {

  // This abstract function should be defined in child class
  // It should check that expr and json match after conversion
  def compare(expr: TlaEx, json: String, indent: Int = -1): Unit

  // compare, while expecting multi-line formatting
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
      """42"""
    )
  }

  test("big int") {
    // int
    compare(
      bigInt(BigInt("9876543210")),
      """{"int":"9876543210"}"""
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
      """{"enum":[42]}"""
    )
  }

  test("singleton set multi-line") {
    // { 42 }
    compareMultiLine(
      enumSet(42),
      """{
        |  "enum": [
        |    42
        |  ]
        |}""".stripMargin
    )
  }

  test("enum") {
    // { 1, 2, 3 }
    compare(
      enumSet(int(1), int(2), int(3)),
      """{"enum":[1,2,3]}"""
    )
  }

  test("enum multi-line") {
    // { 1, 2, 3 }
    compareMultiLine(
      enumSet(int(1), int(2), int(3)),
      """{
        |  "enum": [
        |    1,
        |    2,
        |    3
        |  ]
        |}""".stripMargin
    )
  }

  test("tuple") {
    // << 1, two, "three" >>
    compare(
      tuple(int(1), name("two"), str("three")),
      """{"tuple":[1,"two",{"str":"three"}]}"""
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
      """{"-":[1,2]}"""
    )
  }

  test("function constructor") {
    // [ x \in S, y \in T |-> x + y ]
    compareMultiLine(
      funDef(plus("x", "y"), "x", "S", "y", "T"),
      """{
        |  "fun": {
        |    "+": [
        |      "x",
        |      "y"
        |    ]
        |  },
        |  "where": [
        |    [
        |      "x",
        |      "S"
        |    ],
        |    [
        |      "y",
        |      "T"
        |    ]
        |  ]
        |}""".stripMargin
    )
  }

  test("recursive function constructor") {
    // [x \in S] == 1 + recFunRef
    compareMultiLine(
      recFunDef(plus(int(1), recFunRef()), "x", "S"),
      """{
        |  "rec-fun": {
        |    "+": [
        |      1,
        |      {
        |        "apply-op": "rec-fun-ref"
        |      }
        |    ]
        |  },
        |  "where": [
        |    [
        |      "x",
        |      "S"
        |    ]
        |  ]
        |}""".stripMargin
    )
  }

  test("function application") {
    // f[e]
    compare(
      appFun("f", "e"),
      """{"apply-fun":"f","arg":"e"}"""
    )
  }

  test("operator application") {
    // A(1,2)
    compare(
      OperEx(TlaOper.apply, "A", 1, 2),
      """{"apply-op":"A","args":[1,2]}"""
    )
  }

  test("double function application") {
    // f[e][g]
    compare(
      appFun(appFun("f", "e"), "g"),
      """{"apply-fun":{"apply-fun":"f","arg":"e"},"arg":"g"}"""
    )
  }

  test("function except") {
    // [f EXCEPT ![k] = v]
    compare(
      except("f", "k", "v"),
      """{"except":"f","where":[["k","v"]]}"""
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
      """{"record":[[{"str":"x1"},"y1"],[{"str":"x2"},"y2"],[{"str":"x3"},"y3"]]}"""
    )
  }

  test("function set") {
    // [S -> T]
    compare(
      funSet(name("S"), name("T")),
      """{"fun-set":["S","T"]}"""
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
      """{"rec-set":[[{"str":"x"},"S"],[{"str":"y"},"T"],[{"str":"z"},"U"]]}"""
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
        |      5
        |    ]
        |  }
        |}""".stripMargin
    )
  }

  test("map") {
    // {x+y: x \in S, y \in T}
    compare(
      map(plus("x", "y"), "x", "S", "y", "T"),
      """{"map":{"+":["x","y"]},"where":[["x","S"],["y","T"]]}"""
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
      """{"CHOOSE":["x","S"],"that":{">":["x",3]}}"""
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
        |      5
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
      """{"CASE":[["guard1","action1"],["guard2","action2"]]}"""
    )
  }

  test("case with other") {
    // CASE guard1 -> action1
    //   [] guard2 -> action2
    //   [] OTHER -> otherAction
    compare(
      caseOther("otherAction", "guard1", "action1", "guard2", "action2"),
      """{"CASE":[["guard1","action1"],["guard2","action2"]],"OTHER":"otherAction"}"""
    )
  }

  test("[A]_x") {
    compare(
      stutt("A", "x"),
      """{"stutter":"A","vars":"x"}"""
    )
  }

  test("<A>_<<x,y>>") {
    compare(
      nostutt("A", tuple("x", "y")),
      """{"nostutter":"A","vars":{"tuple":["x","y"]}}"""
    )
  }

  test("WF_x(A)") {
    compare(
      WF("x", "A"),
      """{"WF":"A","vars":"x"}"""
    )
  }

  test("SF_<<x,y>>(A)") {
    compare(
      SF(tuple("x", "y"), "A"),
      """{"SF":"A","vars":{"tuple":["x","y"]}}"""
    )
  }

  test("L2 :: 1") {
    compare(
      label(int(1), "L2"),
      """{"int":"1","label":{"name":"L2","args":[]}}"""
    )
  }

  test("L2 :: x") {
    compare(
      label(name("x"), "L2"),
      """{"id":"x","label":{"name":"L2","args":[]}}"""
    )
  }

  test("L2(a, b) :: f(x+y)>2") {
    compare(
      label(appFun("f", gt(plus("x","y"),2)), "L2", "a", "b"),
      """{"apply-fun":"f","arg":{">":[{"+":["x","y"]},2]},"label":{"name":"L2","args":["a","b"]}}"""
    )
  }

  test("LET A == 1 IN A") {
    val aDecl = TlaOperDecl("A", List(), 1)
    compare(
      letIn(appDecl(aDecl), aDecl),
      """{"LET":[{"OPERATOR":"A","body":1}],"IN":{"apply-op":"A"}}"""
    )
  }

  test("LET A(x, y) == x + y IN A(1,2)") {
    // <A>_vars
    val decl = TlaOperDecl("A",
      List(SimpleFormalParam("x"), SimpleFormalParam("y")),
      plus("x", "y"))
    compare(
      letIn(appDecl(decl, int(1), int(2)), decl),
      """{"LET":[{"OPERATOR":"A","body":{"+":["x","y"]},"params":[{"name":"x","arity":0},{"name":"y","arity":0}]}],"IN":{"apply-op":"A","args":[1,2]}}"""
    )
  }

  test("LET A(x, y) == x + 1 IN B(x, y) == x - y IN A(1, 2) * B(3, 4)") {
    // <A>_vars
    val decl1 = TlaOperDecl("A",
      List(SimpleFormalParam("x"), SimpleFormalParam("y")),
      plus("x", "y"))
    val decl2 = TlaOperDecl("B",
      List(SimpleFormalParam("x"), SimpleFormalParam("y")),
      minus("x", "y"))
    compareMultiLine(
      letIn(
        mult(
          appDecl(decl1, int(1), int(2)),
          appDecl(decl2, int(3), int(4))),
        decl1, decl2),
      """{
        |  "LET": [
        |    {
        |      "OPERATOR": "A",
        |      "body": {
        |        "+": [
        |          "x",
        |          "y"
        |        ]
        |      },
        |      "params": [
        |        {
        |          "name": "x",
        |          "arity": 0
        |        },
        |        {
        |          "name": "y",
        |          "arity": 0
        |        }
        |      ]
        |    },
        |    {
        |      "OPERATOR": "B",
        |      "body": {
        |        "-": [
        |          "x",
        |          "y"
        |        ]
        |      },
        |      "params": [
        |        {
        |          "name": "x",
        |          "arity": 0
        |        },
        |        {
        |          "name": "y",
        |          "arity": 0
        |        }
        |      ]
        |    }
        |  ],
        |  "IN": {
        |    "*": [
        |      {
        |        "apply-op": "A",
        |        "args": [
        |          1,
        |          2
        |        ]
        |      },
        |      {
        |        "apply-op": "B",
        |        "args": [
        |          3,
        |          4
        |        ]
        |      }
        |    ]
        |  }
        |}""".stripMargin
    )
  }
}
