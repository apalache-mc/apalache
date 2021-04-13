package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.FunSuite
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * <p>Geeneric set of tests for conversion between TLA and JSON.</p>
 *
 * @author Andrey Kuprianov
 */

@RunWith(classOf[JUnitRunner])
abstract class TestJson extends FunSuite {

  // This abstract function should be defined in child class
  // It should check that mod and json match after conversion
  def compareModule(mod: TlaModule, json: String, indent: Int = -1): Unit

  // This abstract function should be defined in child class
  // It should check that expr and json match after conversion
  def compare(expr: TlaEx, json: String, indent: Int = -1): Unit

  // compare, while expecting multi-line formatting
  def compareMultiLine(ex: TlaEx, expected: String): Unit =
    compare(ex, expected, 2)

  def compareModuleMultiLine(mod: TlaModule, expected: String): Unit =
    compareModule(mod, expected, 2)

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
        prime(name("awesome")),
        """{"prime":"awesome"}"""
    )
  }

  test("empty set") {
    // { }
    compare(
        enumSet(),
        """{"enumSet":[]}"""
    )
  }
  //
  test("singleton set") {
    // { 42 }
    compare(
        enumSet(int(42)),
        """{"enumSet":[42]}"""
    )
  }

  test("singleton set multi-line") {
    // { 42 }
    compareMultiLine(
        enumSet(int(42)),
        """{
        |  "enumSet": [
        |    42
        |  ]
        |}""".stripMargin
    )
  }

  test("enum") {
    // { 1, 2, 3 }
    compare(
        enumSet(int(1), int(2), int(3)),
        """{"enumSet":[1,2,3]}"""
    )
  }

  test("enum multi-line") {
    // { 1, 2, 3 }
    compareMultiLine(
        enumSet(int(1), int(2), int(3)),
        """{
        |  "enumSet": [
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
        """{"minus":1,"arg":2}"""
    )
  }

  test("function constructor") {
    // [ x \in S, y \in T |-> x + y ]
    compareMultiLine(
        funDef(plus(name("x"), name("y")), name("x"), name("S"), name("y"), name("T")),
        """{
        |  "funDef": {
        |    "plus": "x",
        |    "arg": "y"
        |  },
        |  "where": [
        |    {
        |      "key": "x",
        |      "value": "S"
        |    },
        |    {
        |      "key": "y",
        |      "value": "T"
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("recursive function constructor") {
    // [x \in S] == 1 + recFunRef
    compare(
        recFunDef(plus(int(1), recFunRef()), name("x"), name("S")),
        """{"recFunDef":{"plus":1,"arg":{"applyOp":"recFunRef","args":[]}},"where":[{"key":"x","value":"S"}]}""".stripMargin
    )
  }

  test("function application") {
    // f[e]
    compare(
        appFun(name("f"), name("e")),
        """{"applyFun":"f","arg":"e"}"""
    )
  }

  test("operator application") {
    // A(1,2)
    compare(
        OperEx(TlaOper.apply, name("A"), int(1), int(2)),
        """{"applyOp":"A","args":[1,2]}"""
    )
  }

  test("double function application") {
    // f[e][g]
    compare(
        appFun(appFun(name("f"), name("e")), name("g")),
        """{"applyFun":{"applyFun":"f","arg":"e"},"arg":"g"}"""
    )
  }

  test("function except") {
    // [f EXCEPT ![k] = v]
    compare(
        except(name("f"), name("k"), name("v")),
        """{"except":"f","where":[{"key":"k","value":"v"}]}"""
    )
  }

  test("record / function enumeration") {
    // [ k_1 |-> v_1, ..., k_n |-> v_n ]
    compare(
        enumFun(
            str("x1"),
            name("y1"),
            str("x2"),
            name("y2"),
            str("x3"),
            name("y3")
        ),
        """{"record":[{"key":{"str":"x1"},"value":"y1"},{"key":{"str":"x2"},"value":"y2"},{"key":{"str":"x3"},"value":"y3"}]}"""
    )
  }

  test("function set") {
    // [S -> T]
    compare(
        funSet(name("S"), name("T")),
        """{"funSet":"S","arg":"T"}"""
    )
  }

  test("record set") {
    // [x: S -> T]
    compare(
        recSet(
            str("x"),
            name("S"),
            str("y"),
            name("T"),
            str("z"),
            name("U")
        ),
        """{"recSet":[{"key":{"str":"x"},"value":"S"},{"key":{"str":"y"},"value":"T"},{"key":{"str":"z"},"value":"U"}]}"""
    )
  }

  test("filter") {
    // {x \in S: P}
    compare(
        filter(name("x"), name("S"), name("P")),
        """{"filter":{"key":"x","value":"S"},"that":"P"}"""
    )
  }

  test("filter with predicate") {
    // {x \in S: P}
    compareMultiLine(
        filter(name("x"), name("S"), lt(name("x"), int(5))),
        """{
        |  "filter": {
        |    "key": "x",
        |    "value": "S"
        |  },
        |  "that": {
        |    "lt": "x",
        |    "arg": 5
        |  }
        |}""".stripMargin
    )
  }

  test("map") {
    // {x+y: x \in S, y \in T}
    compare(
        map(plus(name("x"), name("y")), name("x"), name("S"), name("y"), name("T")),
        """{"map":{"plus":"x","arg":"y"},"where":[{"key":"x","value":"S"},{"key":"y","value":"T"}]}"""
    )
  }

  test("exists bounded") {
    // \E x \in S : P
    compare(
        exists(name("x"), name("S"), name("P")),
        """{"existsBounded":{"key":"x","value":"S"},"that":"P"}"""
    )
  }

  test("exists unbounded") {
    // \E x : P
    compare(
        exists(name("x"), name("P")),
        """{"exists":"x","that":"P"}"""
    )
  }

  test("choose bounded") {
    // CHOOSE x \in S : x > 3
    compare(
        choose(name("x"), name("S"), gt(name("x"), int(3))),
        """{"chooseBounded":{"key":"x","value":"S"},"that":{"gt":"x","arg":3}}"""
    )
  }

  test("choose unbounded") {
    // CHOOSE <<x, y>> : x + y <= 5
    compareMultiLine(
        choose(tuple(name("x"), name("y")), le(plus(name("x"), name("y")), int(5))),
        """{
        |  "choose": {
        |    "tuple": [
        |      "x",
        |      "y"
        |    ]
        |  },
        |  "that": {
        |    "le": {
        |      "plus": "x",
        |      "arg": "y"
        |    },
        |    "arg": 5
        |  }
        |}""".stripMargin
    )
  }

  test("if then else") {
    // \E x \in S : P
    compare(
        ite(name("p"), name("x"), name("y")),
        """{"if":"p","then":"x","else":"y"}"""
    )
  }

  test("case split") {
    // CASE guard1 -> action1
    //   [] guard2 -> action2
    compare(
        caseSplit(name("guard1"), name("action1"), name("guard2"), name("action2")),
        """{"case":[{"key":"guard1","value":"action1"},{"key":"guard2","value":"action2"}]}"""
    )
  }

  test("case with other") {
    // CASE guard1 -> action1
    //   [] guard2 -> action2
    //   [] OTHER -> otherAction
    compare(
        caseOther(name("otherAction"), name("guard1"), name("action1"), name("guard2"), name("action2")),
        """{"case":[{"key":"guard1","value":"action1"},{"key":"guard2","value":"action2"}],"other":"otherAction"}"""
    )
  }

  test("[A]_x") {
    compare(
        stutt(name("A"), name("x")),
        """{"stutter":"A","vars":"x"}"""
    )
  }

  test("<A>_<<x,y>>") {
    compare(
        nostutt(name("A"), tuple(name("x"), name("y"))),
        """{"nostutter":"A","vars":{"tuple":["x","y"]}}"""
    )
  }

  test("WF_x(A)") {
    compare(
        WF(name("x"), name("A")),
        """{"weakFairness":"A","vars":"x"}"""
    )
  }

  test("SF_<<x,y>>(A)") {
    compare(
        SF(tuple(name("x"), name("y")), name("A")),
        """{"strongFairness":"A","vars":{"tuple":["x","y"]}}"""
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
        label(appFun(name("f"), gt(plus(name("x"), name("y")), int(2))), "L2", "a", "b"),
        """{"applyFun":"f","arg":{"gt":{"plus":"x","arg":"y"},"arg":2},"label":{"name":"L2","args":["a","b"]}}"""
    )
  }

  test("LET A == 1 IN A") {
    val aDecl = TlaOperDecl("A", List(), int(1))
    compare(
        letIn(appDecl(aDecl), aDecl),
        """{"let":[{"operator":"A","body":1,"params":[]}],"body":{"applyOp":"A","args":[]}}"""
    )
  }

  test("LET A(x, y) == x + y IN A(1,2)") {
    // <A>_vars
    val decl = TlaOperDecl("A", List(OperParam("x"), OperParam("y")), plus(name("x"), name("y")))
    compare(
        letIn(appDecl(decl, int(1), int(2)), decl),
        """{"let":[{"operator":"A","body":{"plus":"x","arg":"y"},"params":[{"name":"x","arity":0},{"name":"y","arity":0}]}],"body":{"applyOp":"A","args":[1,2]}}"""
    )
  }

  test("LET A(x, y) == x + 1 IN B(x, y) == x - y IN A(1, 2) * B(3, 4)") {
    // <A>_vars
    val decl1 = TlaOperDecl("A", List(OperParam("x"), OperParam("y")), plus(name("x"), name("y")))
    val decl2 = TlaOperDecl("B", List(OperParam("x"), OperParam("y")), minus(name("x"), name("y")))
    compareMultiLine(
        letIn(mult(appDecl(decl1, int(1), int(2)), appDecl(decl2, int(3), int(4))), decl1, decl2),
        """{
        |  "let": [
        |    {
        |      "operator": "A",
        |      "body": {
        |        "plus": "x",
        |        "arg": "y"
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
        |      "operator": "B",
        |      "body": {
        |        "minus": "x",
        |        "arg": "y"
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
        |  "body": {
        |    "mult": {
        |      "applyOp": "A",
        |      "args": [
        |        1,
        |        2
        |      ]
        |    },
        |    "arg": {
        |      "applyOp": "B",
        |      "args": [
        |        3,
        |        4
        |      ]
        |    }
        |  }
        |}""".stripMargin
    )
  }

  test("empty module") {
    // awesome
    compareModule(
        new TlaModule("TEST", List()),
        """{"module":"TEST","declarations":[]}"""
    )
  }

  test("module trivial") {
    // awesome
    compareModule(
        new TlaModule("trivial",
            List(
                TlaOperDecl("A", List(), int(42))
            )),
        """{"module":"trivial","declarations":[{"operator":"A","body":42,"params":[]}]}"""
    )
  }

  test("module simpleOperator") {
    // awesome
    compareModuleMultiLine(
        new TlaModule("simpleOperator",
            List(
                TlaOperDecl("A", List(OperParam("age")), gt(name("age"), int(42)))
            )),
        """{
        |  "module": "simpleOperator",
        |  "declarations": [
        |    {
        |      "operator": "A",
        |      "body": {
        |        "gt": "age",
        |        "arg": 42
        |      },
        |      "params": [
        |        {
        |          "name": "age",
        |          "arity": 0
        |        }
        |      ]
        |    }
        |  ]
        |}""".stripMargin
    )
  }

  test("module level2Operators") {
    // awesome
    val aDecl = TlaOperDecl("A", List(OperParam("i"), OperParam("j"), OperParam("f", 1)),
        OperEx(TlaOper.apply, NameEx("f"), OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j"))))
    val bDecl = TlaOperDecl("B", List(OperParam("y")), NameEx("y"))
    compareModuleMultiLine(
        new TlaModule("level2Operators",
            List(
                aDecl,
                bDecl,
                TlaOperDecl("C", List(OperParam("z")), appDecl(aDecl, int(0), NameEx("z"), appDecl(bDecl, int(1))))
            )),
        """{
        |  "module": "level2Operators",
        |  "declarations": [
        |    {
        |      "operator": "A",
        |      "body": {
        |        "applyOp": "f",
        |        "args": [
        |          {
        |            "cup": "i",
        |            "arg": "j"
        |          }
        |        ]
        |      },
        |      "params": [
        |        {
        |          "name": "i",
        |          "arity": 0
        |        },
        |        {
        |          "name": "j",
        |          "arity": 0
        |        },
        |        {
        |          "name": "f",
        |          "arity": 1
        |        }
        |      ]
        |    },
        |    {
        |      "operator": "B",
        |      "body": "y",
        |      "params": [
        |        {
        |          "name": "y",
        |          "arity": 0
        |        }
        |      ]
        |    },
        |    {
        |      "operator": "C",
        |      "body": {
        |        "applyOp": "A",
        |        "args": [
        |          0,
        |          "z",
        |          {
        |            "applyOp": "B",
        |            "args": [
        |              1
        |            ]
        |          }
        |        ]
        |      },
        |      "params": [
        |        {
        |          "name": "z",
        |          "arity": 0
        |        }
        |      ]
        |    }
        |  ]
        |}""".stripMargin
    )
  }
}
