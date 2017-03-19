package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.{OperEx, _}
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

import scala.io.Source

/**
  * Tests for the SANY importer.
  *
  * @author konnov
  */
@RunWith(classOf[JUnitRunner])
class TestSanyImporter extends FunSuite {

  test("empty module") {
    val text =
      """---- MODULE justASimpleTest ----
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("justASimpleTest", Source.fromString(text))
    assert("justASimpleTest" == rootName)
  }

  test("one variable") {
    val text =
      """---- MODULE onevar ----
        |VARIABLE x
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("onevar", Source.fromString(text))
    val mod = expectSingleModule("onevar", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case vd: TlaVarDecl =>
        assert("x" == vd.name)

      case _ =>
        fail("Expected a declaration of variable x")
    }
  }

  test("one constant") {
    val text =
      """---- MODULE oneconst ----
        |CONSTANT n
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("oneconst", Source.fromString(text))
    val mod = expectSingleModule("oneconst", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case constDecl: TlaConstDecl =>
        assert("n" == constDecl.name)
    }
  }

  test("constant operator (int)") {
    val text =
      """---- MODULE constop ----
        |MyOp == 1
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaInt(1)) == actionDecl.body)
    }
  }

  test("constant operator (decimal)") {
    val text =
      """---- MODULE constop ----
        |MyOp == 123.456
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaDecimal(BigDecimal("123.456"))) == actionDecl.body)
    }
  }

  test("constant operator (string)") {
    val text =
      """---- MODULE constop ----
        |MyOp == "Hello"
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaStr("Hello")) == actionDecl.body)
    }
  }

  test("constant operator (FALSE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == FALSE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(false)) == actionDecl.body)
    }
  }

  test("constant operator (TRUE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(true)) == actionDecl.body)
    }
  }

  test("constant operator (a single variable)") {
    val text =
      """---- MODULE constop ----
        |VARIABLE x
        |
        |MyOp == x
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(2 == mod.declarations.size)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(NameEx("x") == actionDecl.body)
    }
  }

  test("constant operator (a single constant)") {
    val text =
      """---- MODULE constop ----
        |CONSTANT n
        |
        |MyOp == n
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(2 == mod.declarations.size)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(NameEx("n") == actionDecl.body)
    }
  }

  test("constant operator (a builtin operator)") {
    val text =
      """---- MODULE builtinop ----
        |MyOp == FALSE \/ TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("builtinop", Source.fromString(text))
    val mod = expectSingleModule("builtinop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue)) == actionDecl.body)
    }
  }

  test("empty set") {
    val text =
      """---- MODULE emptyset ----
        |MyOp == {}
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("emptyset", Source.fromString(text))
    val mod = expectSingleModule("emptyset", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaEmptySet) == actionDecl.body)
    }
  }


  test("constant operator (a builtin op and variables)") {
    val text =
      """---- MODULE builtinop ----
        |VARIABLE x
        |MyOp == x /\ TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter().load("builtinop", Source.fromString(text))
    val mod = expectSingleModule("builtinop", rootName, modules)
    assert(2 == mod.declarations.size)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaBoolOper.and, NameEx("x"), ValEx(TlaTrue)) == actionDecl.body)
    }
  }

  test("built-in operators") {
    // Following the operator table from tla2sany.semantic.BuiltInLevel.LevelData.
    // Here we test the very basic application of every operator.
    // For more advanced expressions, see the individual tests for each operator.
    val text =
    """---- MODULE builtins ----
      |VARIABLES x
      |True == TRUE
      |
      |Eq == FALSE = TRUE
      |Ne == FALSE /= TRUE
      |Prime == x'
      |Not == ~x
      |Or == FALSE \/ TRUE
      |And == FALSE /\ TRUE
      |Equiv == FALSE <=> TRUE
      |Implies == FALSE => TRUE
      |Subset == SUBSET x
      |Union == UNION x
      |Domain == DOMAIN x
      |Subseteq == x \subseteq x
      |In == x \in x
      |Notin == x \notin x
      |Setminus == x \ x
      |Cap == x \cap x
      |Cup == x \cup x
      |Times == x \X x
      |LeadsTo == TRUE ~> TRUE
      |Box == []TRUE
      |Diamond == <>TRUE
      |Enabled == ENABLED x
      |Unchanged == UNCHANGED x
      |Cdot == (True \cdot True)
      |Guarantees == True -+-> True
      |Angleact == <<True>>_x
      |BoundedChoose == CHOOSE y \in x: TRUE
      |BoundedExists == \E y \in x: TRUE
      |BoundedForall == \A y \in x: TRUE
      |CartesianProd == x \X x \X x
      |Pair == <<1, 2>>
      |Tuple == <<1, 2, 3>>
      |Case == CASE 1 -> 2 [] 3 -> 4 [] 5 -> 6
      |CaseOther == CASE 1 -> 2 [] 3 -> 4 [] 5 -> 6 [] OTHER -> 7
      |ConjList == /\ FALSE
      |            /\ TRUE
      |            /\ FALSE
      |DisjList == \/ FALSE
      |            \/ TRUE
      |            \/ FALSE
      |Except == [ x EXCEPT ![0] = 1 ]
      |FcnApply == x[1]
      |FcnCtor == [ y \in x |-> y \cup y ]
      |IfThenElse == IF TRUE THEN FALSE ELSE TRUE
      |RcdCtor == [ a |-> 1, b |-> 2 ]
      |RcdSelect == x.foo
      |SetEnumerate == { 1, 2, 3 }
      |SetOfFcns == [ x -> x ]
      |SetOfRcds == [ a: x, b: x ]
      |StrongFairness == SF_x(True)
      |WeakFairness == WF_x(True)
      |SquareAct == [True]_x
      |TemporalExists == \EE y : True
      |TemporalForall == \AA y : True
      |UnboundedChoose == CHOOSE y: TRUE
      |UnboundedExists == \E y: TRUE
      |UnboundedForall == \A y: TRUE
      |SetOfAll == { 1: y \in x }
      |SubsetOf == { y \in x: TRUE }
      |Boolean == BOOLEAN
      |String == STRING
      |
      |================================
      |""".stripMargin

    // TODO: implement the following functions
    //        |nonRecursiveFcnSpec[y \in x] == y \cup x
    //        |recursiveFcnSpec[y \in x] == recursiveFcnSpec[y]

    // TODO: figure out what this operator is
    //
    //        |TemporalWhile == ????

    val (rootName, modules) = new SanyImporter().load("builtins", Source.fromString(text))
    val mod = expectSingleModule("builtins", rootName, modules)
    val root = modules(rootName)

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    val trueOperDecl = mod.declarations(1)
    assertTlaDecl("True", ValEx(TlaTrue))
    val trueOper = TlaOperDecl("True", List(), ValEx(TlaTrue)).operator
    assert(OperEx(trueOper) == OperEx(trueOper))


    assertTlaDecl("Eq", OperEx(TlaOper.eq, ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("Ne", OperEx(TlaOper.ne, ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("Prime", OperEx(TlaActionOper.prime, NameEx("x")))
    assertTlaDecl("Not", OperEx(TlaBoolOper.not, NameEx("x")))
    assertTlaDecl("Or", OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("And", OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("Equiv", OperEx(TlaBoolOper.equiv, ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("Implies", OperEx(TlaBoolOper.implies, ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("Subset", OperEx(TlaSetOper.SUBSET, NameEx("x")))
    assertTlaDecl("Union", OperEx(TlaSetOper.union, NameEx("x")))
    assertTlaDecl("Domain", OperEx(TlaFunOper.domain, NameEx("x")))
    assertTlaDecl("Subseteq", OperEx(TlaSetOper.subseteq, NameEx("x"), NameEx("x")))
    assertTlaDecl("In", OperEx(TlaSetOper.in, NameEx("x"), NameEx("x")))
    assertTlaDecl("Notin", OperEx(TlaSetOper.notin, NameEx("x"), NameEx("x")))
    assertTlaDecl("Setminus", OperEx(TlaSetOper.setminus, NameEx("x"), NameEx("x")))
    assertTlaDecl("Cap", OperEx(TlaSetOper.cap, NameEx("x"), NameEx("x")))
    assertTlaDecl("Cup", OperEx(TlaSetOper.cup, NameEx("x"), NameEx("x")))
    assertTlaDecl("Times", OperEx(TlaSetOper.times, NameEx("x"), NameEx("x")))
    assertTlaDecl("LeadsTo", OperEx(TlaTempOper.leadsTo, ValEx(TlaTrue), ValEx(TlaTrue)))
    assertTlaDecl("Box", OperEx(TlaTempOper.box, ValEx(TlaTrue)))
    assertTlaDecl("Diamond", OperEx(TlaTempOper.diamond, ValEx(TlaTrue)))
    assertTlaDecl("Enabled", OperEx(TlaActionOper.enabled, NameEx("x")))
    assertTlaDecl("Unchanged", OperEx(TlaActionOper.unchanged, NameEx("x")))
    assertTlaDecl("Cdot", OperEx(TlaActionOper.composition, OperEx(trueOper), OperEx(trueOper)))
    assertTlaDecl("Guarantees",
      OperEx(TlaTempOper.guarantees, OperEx(trueOper), OperEx(trueOper)))
    assertTlaDecl("Angleact",
      OperEx(TlaActionOper.nostutter, OperEx(trueOper), NameEx("x")))
    assertTlaDecl("BoundedChoose",
      OperEx(TlaOper.chooseBounded, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    assertTlaDecl("BoundedExists",
      OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    assertTlaDecl("BoundedForall",
      OperEx(TlaBoolOper.forall, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    assertTlaDecl("CartesianProd",
      OperEx(TlaSetOper.times, NameEx("x"), NameEx("x"), NameEx("x")))
    assertTlaDecl("Pair", OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
    assertTlaDecl("Tuple",
      OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    assertTlaDecl("Case",
      OperEx(TlaControlOper.caseNoOther, 1.to(6).map(i => ValEx(TlaInt(i))): _*))
    assertTlaDecl("CaseOther",
      OperEx(TlaControlOper.caseWithOther, (7 +: 1.to(6)).map(i => ValEx(TlaInt(i))): _*))
    assertTlaDecl("ConjList",
      OperEx(TlaBoolOper.and, List(TlaFalse, TlaTrue, TlaFalse).map(b => ValEx(b)): _*))
    assertTlaDecl("DisjList",
      OperEx(TlaBoolOper.or, List(TlaFalse, TlaTrue, TlaFalse).map(b => ValEx(b)): _*))
    assertTlaDecl("Except",
      OperEx(TlaFunOper.except,
        NameEx("x"), TlaFunOper.mkTuple(ValEx(TlaInt(0))), ValEx(TlaInt(1))
      ))
    assertTlaDecl("FcnApply", OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(1))))
    val cup = OperEx(TlaSetOper.cup, NameEx("y"), NameEx("y"))
    assertTlaDecl("FcnCtor",
      OperEx(TlaFunOper.funDef, cup, NameEx("y"), NameEx("x")))
    assertTlaDecl("IfThenElse",
      OperEx(TlaControlOper.ifThenElse, ValEx(TlaTrue), ValEx(TlaFalse), ValEx(TlaTrue)))
    assertTlaDecl("RcdCtor",
      OperEx(TlaFunOper.enum,
        ValEx(TlaStr("a")), ValEx(TlaInt(1)), ValEx(TlaStr("b")), ValEx(TlaInt(2))))
    assertTlaDecl("RcdSelect",
      OperEx(TlaFunOper.app,
        NameEx("x"), ValEx(TlaStr("foo"))))
    assertTlaDecl("SetEnumerate",
      OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    assertTlaDecl("SetOfFcns", OperEx(TlaSetOper.funSet, NameEx("x"), NameEx("x")))
    assertTlaDecl("SetOfRcds",
      OperEx(TlaSetOper.recSet,
        ValEx(TlaStr("a")), NameEx("x"), ValEx(TlaStr("b")), NameEx("x")))
    assertTlaDecl("StrongFairness",
      OperEx(TlaTempOper.strongFairness, NameEx("x"), OperEx(trueOper)))
    assertTlaDecl("WeakFairness",
      OperEx(TlaTempOper.weakFairness, NameEx("x"), OperEx(trueOper)))
    assertTlaDecl("SquareAct",
      OperEx(TlaActionOper.stutter, OperEx(trueOper), NameEx("x")))
    assertTlaDecl("TemporalExists",
      OperEx(TlaTempOper.EE, NameEx("y"), OperEx(trueOper)))
    assertTlaDecl("TemporalForall",
      OperEx(TlaTempOper.AA, NameEx("y"), OperEx(trueOper)))
    assertTlaDecl("UnboundedChoose",
      OperEx(TlaOper.chooseUnbounded, NameEx("y"), ValEx(TlaTrue)))
    assertTlaDecl("UnboundedExists",
      OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaTrue)))
    assertTlaDecl("UnboundedForall",
      OperEx(TlaBoolOper.forallUnbounded, NameEx("y"), ValEx(TlaTrue)))
    assertTlaDecl("SetOfAll",
      OperEx(TlaSetOper.map, ValEx(TlaInt(1)), NameEx("y"), NameEx("x")))
    assertTlaDecl("SubsetOf",
      OperEx(TlaSetOper.filter, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    assertTlaDecl("Boolean", ValEx(TlaBoolSet))
    assertTlaDecl("String", ValEx(TlaStrSet))
  }

  test("funCtor quantifiers") {
    // One can write tricky combinations of bound variables in TLA+.
    // We translate all of them uniformly:
    //   every quantified expression has exactly one bound variable or a tuple of variables.
    val text =
    """---- MODULE composite ----
      |VARIABLE X, Z
      |Q1 == \E x \in X: \E y \in X: TRUE
      |Q2 == \E x, y \in X: TRUE
      |Q3 == \E x, y \in X, z \in Z: TRUE
      |Q4 == \E x, y \in X, <<a, b>> \in Z, z \in Z: TRUE
      |Q5 == \E x, y: TRUE
      |================================
      |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("composite", Source.fromString(text))
    val mod = expectSingleModule("composite", rootName, modules)

    def assertTlaDecl(name: String, body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(0 == d.formalParams.length)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("Q1",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue))))(mod.declarations(2))
    assertTlaDecl("Q2",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue))))(mod.declarations(3))
    assertTlaDecl("Q3",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
            ValEx(TlaTrue)))))(mod.declarations(4))
    assertTlaDecl("Q4",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")), NameEx("Z"),
            OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
              ValEx(TlaTrue))))))(mod.declarations(5))
    assertTlaDecl("Q5",
      OperEx(TlaBoolOper.existsUnbounded, NameEx("x"),
        OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaTrue))))(mod.declarations(6))
  }

  test("complex updates") {
    // One can write tricky combinations of EXCEPT arguments.
    val text =
      """---- MODULE updates ----
        |VARIABLE f
        |E1 == [ f EXCEPT ![0] = 1, ![2] = 3 ]
        |E2 == [ f EXCEPT ![0][1][2] = 3 ]
        |E3 == [ f EXCEPT ![0,1,2] = 3 ]
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("updates", Source.fromString(text))
    val mod = expectSingleModule("updates", rootName, modules)

    def assertTlaDecl(name: String, body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(0 == d.formalParams.length)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("E1",
      OperEx(TlaFunOper.except,
        NameEx("f"),
        TlaFunOper.mkTuple(ValEx(TlaInt(0))), ValEx(TlaInt(1)),
        TlaFunOper.mkTuple(ValEx(TlaInt(2))), ValEx(TlaInt(3))
      ))(mod.declarations(1))
    assertTlaDecl("E2",
      OperEx(TlaFunOper.except,
        NameEx("f"),
        TlaFunOper.mkTuple(ValEx(TlaInt(0)), ValEx(TlaInt(1)), ValEx(TlaInt(2))),
        ValEx(TlaInt(3))
      ))(mod.declarations(2))
    assertTlaDecl("E3",
      OperEx(TlaFunOper.except,
        NameEx("f"),
        TlaFunOper.mkTuple(TlaFunOper.mkTuple(ValEx(TlaInt(0)), ValEx(TlaInt(1)), ValEx(TlaInt(2)))),
          ValEx(TlaInt(3))
      ))(mod.declarations(3))
  }

  test("complex record selects") {
    // Testing that multiple field accesses work as expected
    val text =
      """---- MODULE selects ----
        |VARIABLE f
        |S1 == f.a.b
        |S2 == f.a.b.c
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("selects", Source.fromString(text))
    val mod = expectSingleModule("selects", rootName, modules)

    def assertTlaDecl(name: String, body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(0 == d.formalParams.length)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("S1",
      OperEx(TlaFunOper.app,
        OperEx(TlaFunOper.app,
          NameEx("f"),
          ValEx(TlaStr("a"))),
        ValEx(TlaStr("b")))
    )(mod.declarations(1))
    assertTlaDecl("S2",
      OperEx(TlaFunOper.app,
        OperEx(TlaFunOper.app,
          OperEx(TlaFunOper.app,
            NameEx("f"),
            ValEx(TlaStr("a"))),
          ValEx(TlaStr("b"))),
        ValEx(TlaStr("c")))
    )(mod.declarations(2))
  }

  test("complex function ctors") {
    // One can write tricky combinations of bound variables in function constructors.
    val text =
      """---- MODULE funCtor ----
        |VARIABLE X, Z
        |C1 == [ x \in X, y \in X |-> TRUE ]
        |C2 == [ x, y \in X |-> TRUE ]
        |C3 == [ x, y \in X, z \in Z |-> TRUE]
        |C4 == [ x, y \in X, <<a, b>> \in Z, z \in Z |-> TRUE ]
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("funCtor", Source.fromString(text))
    val mod = expectSingleModule("funCtor", rootName, modules)

    def assertTlaDecl(name: String, body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(0 == d.formalParams.length)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("C1",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X")))(mod.declarations(2))
    assertTlaDecl("C2",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X")))(mod.declarations(3))
    assertTlaDecl("C3",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        NameEx("z"), NameEx("Z")
      ))(mod.declarations(4))
    assertTlaDecl("C4",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        TlaFunOper.mkTuple(NameEx("a"), NameEx("b")), NameEx("Z"),
        NameEx("z"), NameEx("Z")
      ))(mod.declarations(5))
  }

  test("level-1 operators") {
    // operators with basic parameters, that is, no operator is passed as a parameter
    val text =
      """---- MODULE level1Operators ----
        |VARIABLE x, y
        |A(i, j) == i \cup j
        |i ** j == i \cap j
        |C == A(1, 2)
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("level1Operators", Source.fromString(text))
    val mod = expectSingleModule("level1Operators", rootName, modules)

    def assertTlaDecl(name: String, params: List[FormalParam], body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(params == d.formalParams)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("A", List(SimpleFormalParam("i"), SimpleFormalParam("j")),
      OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j")))(mod.declarations(2))
    assertTlaDecl("**", List(SimpleFormalParam("i"), SimpleFormalParam("j")),
      OperEx(TlaSetOper.cap, NameEx("i"), NameEx("j")))(mod.declarations(3))
    val aDecl = mod.declarations(2).asInstanceOf[TlaOperDecl]
    assertTlaDecl("C", List(),
      OperEx(aDecl.operator, ValEx(TlaInt(1)), ValEx(TlaInt(2))))(mod.declarations(4))
  }

  test("level-2 operators") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE level2Operators ----
        |VARIABLE x, y
        |A(i, j, f(_)) == f(i \cup j)
        |B(z) == z
        |C == A(0, 1, B)
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("level2Operators", Source.fromString(text))
    val mod = expectSingleModule("level2Operators", rootName, modules)

    def assertTlaDecl(name: String, params: List[FormalParam], body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(params == d.formalParams)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("A",
      List(SimpleFormalParam("i"), SimpleFormalParam("j"), OperFormalParam("f", FixedArity(1))),
      OperEx(OperFormalParamOper("f", 1),
        OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j")))) (mod.declarations(2))
    val aDecl = mod.declarations(2).asInstanceOf[TlaOperDecl]
    assertTlaDecl("C", List(),
      OperEx(aDecl.operator, ValEx(TlaInt(0)), ValEx(TlaInt(1)), NameEx("B")))(mod.declarations(4))
  }

  test("let-in") {
    val text =
      """---- MODULE let ----
        |A ==
        |  LET X == 1
        |  Y(a) == a
        |  Z(f(_), a) == f(a)
        |  IN X
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("let", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find { _.name == "A" } match {
      case Some(TlaOperDecl(_, _, OperEx(o: LetInOper, body))) =>
        assert(3 == o.defs.length)
        val xDecl = o.defs.head
        assert("X" == xDecl.name)
        val yDecl = o.defs(1)
        assert(TlaOperDecl("Y",
          List(SimpleFormalParam("a")),
          NameEx("a")) == yDecl)
        val zDecl = o.defs(2)
        zDecl match {
          case TlaOperDecl("Z", List(OperFormalParam("f", FixedArity(1)), SimpleFormalParam("a")), _) =>
            assert(OperEx(new OperFormalParamOper(OperFormalParam("f", FixedArity(1))),
              NameEx("a")) == zDecl.body)
        }
        assert(0 == xDecl.formalParams.length)
        assert(ValEx(TlaInt(1)) == xDecl.body)
        // although "X" might seem to be a variable, it is actually an operator without any arguments
        assert(OperEx(xDecl.operator) == body)
    }
  }

  // LET-IN with recursive operators
  test("let-in-rec") {
    val text =
      """---- MODULE let ----
        |A ==
        |  LET f[x \in BOOLEAN] == f[x]
        |   RECURSIVE X
        |    X == X
        |  IN X
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("let", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find { _.name == "A" } match {
      case Some(TlaOperDecl(_, _, OperEx(o: LetInOper, body))) =>
        assert(2 == o.defs.length)
        val fDecl = o.defs.head
        assert("f" == fDecl.name)
        val expectedBody =
          OperEx(TlaFunOper.funDef,
            OperEx(TlaFunOper.app,
              OperEx(OperFormalParamOper("f", 0)),
              NameEx("x")),
            NameEx("x"),
            ValEx(TlaBoolSet)
          )

        assert(expectedBody == fDecl.body)
        val xDecl = o.defs(1)
        assert("X" == xDecl.name)
        assert(OperEx(OperFormalParamOper("X", 0)) == xDecl.body)
        assert(OperEx(xDecl.operator) == body)
    }
  }

  test("recursive operators") {
    val text =
      """---- MODULE recOpers ----
        |EXTENDS Naturals
        |
        |CONSTANT S
        |RECURSIVE R(_)
        |R(n) == R(n)
        |RECURSIVE A(_), B(_), C(_)
        |A(n) == B(n)
        |B(n) == C(n)
        |C(n) == A(n)
        |
        |D(n) == A(n)
        |
        |RECURSIVE X
        |X == X
        |
        |RECURSIVE F(_)
        |F(n) == IF n = 0 THEN 1 ELSE n * F(n - 1)
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("recOpers", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def assertRec(name: String, nparams: Int, expectedBody: TlaEx) = {
      root.declarations.find { _.name == name } match {
        case Some(d: TlaRecOperDecl) =>
          // We expect that R in the declaration body is referred by a formal parameter with the same name R.
          // The caveat here is that the formal parameter R does not appear in the list of the R's formal parameters,
          // but it is accessible via the field recParam.
          val recParam = OperFormalParam(name, FixedArity(nparams))
          assert(recParam == d.recParam)
          val RInTheBody = new OperFormalParamOper(recParam)
          assert(d.body == expectedBody)

        case _ =>
          fail("expected TlaRecOperDecl")
      }
    }

    // in the recursive sections, the calls to recursive operators should be replaced with OperFormalParam(...)
    assertRec("R", 1,
      OperEx(OperFormalParamOper("R", 1), NameEx("n")))

    assertRec("A", 1,
      OperEx(OperFormalParamOper("B", 1), NameEx("n")))
    assertRec("B", 1,
      OperEx(OperFormalParamOper("C", 1), NameEx("n")))
    assertRec("C", 1,
      OperEx(OperFormalParamOper("A", 1), NameEx("n")))

    assertRec("X", 0,
      OperEx(OperFormalParamOper("X", 0)))

    // however, in non-recursive sections, the calls to recursive operators are just normal OperEx(operator, ...)
    root.declarations.find { _.name == "D" } match {
      case Some(d: TlaOperDecl) =>
        val A = root.declarations.find { _.name == "A" }.get.asInstanceOf[TlaOperDecl]
        assert(OperEx(A.operator, NameEx("n")) == d.body)

      case _ =>
        fail("Expected TlaOperDecl")
    }

    // of course, we want to see the factorial
    root.declarations.find { _.name == "F"} match {
      case Some(d: TlaRecOperDecl) =>
        // We expect that F in the declaration body is referred by a formal parameter with the same name F.
        // The caveat here is that the formal parameter F does not appear in the list of the F's formal parameters,
        // but it is accessible via the field recParam.
        val recParam = OperFormalParam("F", FixedArity(1))
        assert(recParam == d.recParam)
        val FInTheBody = new OperFormalParamOper(recParam)
        val ite = OperEx(TlaControlOper.ifThenElse,
          OperEx(TlaOper.eq, NameEx("n"), ValEx(TlaInt(0))),
          ValEx(TlaInt(1)),
          OperEx(TlaArithOper.mult, NameEx("n"),
              OperEx(FInTheBody, OperEx(TlaArithOper.minus, NameEx("n"), ValEx(TlaInt(1)))))
        )
        assert(d.body == ite)

      case _ =>
        fail("expected TlaRecOperDecl")
    }
  }

  test("global-funs") {
    val text =
      """---- MODULE globalFuns ----
        |CONSTANT S
        |nonRecFun[x \in S] == x
        |recFun[x \in S] == recFun[x]
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("globalFuns", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    // a non-recursive function becomes a nullary operator that always returns an equivalent function
    assertTlaDecl("nonRecFun",
      OperEx(TlaFunOper.funDef, NameEx("x"), NameEx("x"), NameEx("S"))
    )

    // a recursive function becomes a recursive nullary operator
    // that returns a function defined w.r.t. the recursive operator

    def assertTlaRecDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaRecOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    assertTlaRecDecl("recFun",
      OperEx(TlaFunOper.funDef,
        OperEx(TlaFunOper.app,
          OperEx(OperFormalParamOper("recFun", 0)),
          NameEx("x")),
        NameEx("x"),
        NameEx("S"))
    )
  }

  test("module imports") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE imports ----
        |EXTENDS Naturals
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("imports", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    // the root module contains its own declarations (none in this test) and the declarations by Naturals
    assert(root.declarations.nonEmpty)
    assert(List("Naturals") == root.imports)
    // check that Naturals were imported properly
    val naturals = modules("Naturals")
    assert(naturals.declarations.nonEmpty)
  }

  test("module nats") {
    // check that the Naturals module is imported properly
    val text =
      """---- MODULE nats ----
        |EXTENDS Naturals
        |NatSet == Nat
        |Plus == 3 + 2
        |Minus == 3 - 2
        |Mult == 3 * 2
        |Power == 3 ^ 2
        |Less == 3 < 2
        |Greater == 3 > 2
        |Leq == 3 <= 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("nats", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    // the root module contains its own declarations and the declarations by Naturals
    assertTlaDecl("NatSet", ValEx(TlaNatSet))
    assertTlaDecl("Plus", OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Minus", OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Mult", OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Power", OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Less", OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Greater", OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Leq", OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Geq", OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Mod", OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Div", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Range", OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))))
  }

  test("module ints") {
    // check that the Integers module is imported properly
    val text =
      """---- MODULE ints ----
        |EXTENDS Integers
        |IntSet == Int
        |Plus == 3 + 2
        |Minus == 3 - 2
        |Mult == 3 * 2
        |Power == 3 ^ 2
        |Less == 3 < 2
        |Greater == 3 > 2
        |Leq == 3 <= 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |UnaryMinus == -2
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("ints", Source.fromString(text))
    assert(3 == modules.size) // Integers extends Naturals
    val root = modules(rootName)

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    // the root module contains its own declarations and the declarations by Integers
    assertTlaDecl("IntSet", ValEx(TlaIntSet))
    assertTlaDecl("Plus", OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Minus", OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Mult", OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Power", OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Less", OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Greater", OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Leq", OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Geq", OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Mod", OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Div", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Range", OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    assertTlaDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
  }

  test("module reals") {
    // check that the Reals module is imported properly
    val text =
      """---- MODULE reals ----
        |EXTENDS Reals
        |RealSet == Real
        |Inf == Infinity
        |Plus == 3 + 2
        |Minus == 3 - 2
        |Mult == 3 * 2
        |Power == 3 ^ 2
        |Less == 3 < 2
        |Greater == 3 > 2
        |Leq == 3 <= 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |UnaryMinus == -2
        |RealDiv == 3 / 2
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("reals", Source.fromString(text))
    assert(4 == modules.size) // Reals include Integers that include Naturals
    val root = modules(rootName)
    // the root module contains its own declarations and the declarations by Integers

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    assertTlaDecl("RealSet", ValEx(TlaRealSet))
    assertTlaDecl("Inf", ValEx(TlaRealInfinity))
    assertTlaDecl("Plus", OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Minus", OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Mult", OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Power", OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Less", OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Greater", OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Leq", OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Geq", OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Mod", OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Div", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    assertTlaDecl("Range", OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    assertTlaDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
    assertTlaDecl("RealDiv", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
  }

  /*
  test("module seqs") {
    // check that the FiniteSets module is imported properly
    val text =
      """---- MODULE sequences ----
        |EXTENDS Sequences
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("sequences", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find { _.name == expectedName} match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    // the root module contains its own declarations and the declarations by FiniteSets
//    assertTlaDecl("IsFinSet", OperEx(TlaFiniteSetOper.isFiniteSet, ValEx(TlaBoolSet)))
//    assertTlaDecl("Card", OperEx(TlaFiniteSetOper.cardinality, ValEx(TlaBoolSet)))
  }

    // FiniteSets extend Sequences, which open the Pandora box... Temporarily disabled.
    test("module finitesets") {
      // check that the FiniteSets module is imported properly
      val text =
        """---- MODULE finitesets ----
          |EXTENDS FiniteSets
          |IsFinSet == IsFiniteSet(BOOLEAN)
          |Card == Cardinality(BOOLEAN)
          |
          |================================
          |""".stripMargin

      val (rootName, modules) = new SanyImporter().load("finitesets", Source.fromString(text))
      assert(2 == modules.size)
      // the root module and naturals
      val root = modules(rootName)

      def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
        root.declarations.find { _.name == expectedName} match {
          case Some(d: TlaOperDecl) =>
            assert(expectedName == d.name)
            assert(0 == d.formalParams.length)
            assert(body == d.body)

          case _ =>
            fail("Expected a TlaDecl")
        }
      }

      // the root module contains its own declarations and the declarations by FiniteSets
      assertTlaDecl("IsFinSet", OperEx(TlaFiniteSetOper.isFiniteSet, ValEx(TlaBoolSet)))
      assertTlaDecl("Card", OperEx(TlaFiniteSetOper.cardinality, ValEx(TlaBoolSet)))
    }
    */

  ////////////////////////////////////////////////////////////////////
  private def expectSingleModule(expectedRootName: String, rootName: String, modules: Map[String, TlaModule]): TlaModule = {
    assert(expectedRootName == rootName)
    assert(1 == modules.size)
    val root = modules.get(rootName)
    root match {
      case Some(mod) =>
        mod

      case None =>
        fail("Module " + rootName + " not found")
    }
  }
}
