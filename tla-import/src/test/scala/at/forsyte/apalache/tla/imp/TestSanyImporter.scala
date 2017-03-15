package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._
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
    val mod = expectModule("onevar", rootName, modules)
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
    val mod = expectModule("oneconst", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("constop", rootName, modules)
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
    val mod = expectModule("builtinop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue)) == actionDecl.body)
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
    val mod = expectModule("builtinop", rootName, modules)
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
    val mod = expectModule("builtins", rootName, modules)

    def assertTlaDecl(name: String, body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(0 == d.formalParams.length)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    val trueOperDecl = mod.declarations(1)
    assertTlaDecl("True", ValEx(TlaTrue))(trueOperDecl)
    val trueOper = TlaOperDecl("True", List(), ValEx(TlaTrue)).operator
    assert(OperEx(trueOper) == OperEx(trueOper))


    assertTlaDecl("Eq", OperEx(TlaOper.eq, ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(2))
    assertTlaDecl("Ne", OperEx(TlaOper.ne, ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(3))
    assertTlaDecl("Prime", OperEx(TlaActionOper.prime, NameEx("x")))(mod.declarations(4))
    assertTlaDecl("Not", OperEx(TlaBoolOper.not, NameEx("x")))(mod.declarations(5))
    assertTlaDecl("Or", OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(6))
    assertTlaDecl("And", OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(7))
    assertTlaDecl("Equiv", OperEx(TlaBoolOper.equiv, ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(8))
    assertTlaDecl("Implies", OperEx(TlaBoolOper.implies, ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(9))
    assertTlaDecl("Subset", OperEx(TlaSetOper.SUBSET, NameEx("x")))(mod.declarations(10))
    assertTlaDecl("Union", OperEx(TlaSetOper.union, NameEx("x")))(mod.declarations(11))
    assertTlaDecl("Domain", OperEx(TlaFunOper.domain, NameEx("x")))(mod.declarations(12))
    assertTlaDecl("Subseteq", OperEx(TlaSetOper.subseteq, NameEx("x"), NameEx("x")))(mod.declarations(13))
    assertTlaDecl("In", OperEx(TlaSetOper.in, NameEx("x"), NameEx("x")))(mod.declarations(14))
    assertTlaDecl("Notin", OperEx(TlaSetOper.notin, NameEx("x"), NameEx("x")))(mod.declarations(15))
    assertTlaDecl("Setminus", OperEx(TlaSetOper.setminus, NameEx("x"), NameEx("x")))(mod.declarations(16))
    assertTlaDecl("Cap", OperEx(TlaSetOper.cap, NameEx("x"), NameEx("x")))(mod.declarations(17))
    assertTlaDecl("Cup", OperEx(TlaSetOper.cup, NameEx("x"), NameEx("x")))(mod.declarations(18))
    assertTlaDecl("Times", OperEx(TlaSetOper.times, NameEx("x"), NameEx("x")))(mod.declarations(19))
    assertTlaDecl("LeadsTo", OperEx(TlaTempOper.leadsTo, ValEx(TlaTrue), ValEx(TlaTrue)))(mod.declarations(20))
    assertTlaDecl("Box", OperEx(TlaTempOper.box, ValEx(TlaTrue)))(mod.declarations(21))
    assertTlaDecl("Diamond", OperEx(TlaTempOper.diamond, ValEx(TlaTrue)))(mod.declarations(22))
    assertTlaDecl("Enabled", OperEx(TlaActionOper.enabled, NameEx("x")))(mod.declarations(23))
    assertTlaDecl("Unchanged", OperEx(TlaActionOper.unchanged, NameEx("x")))(mod.declarations(24))
    assertTlaDecl("Cdot", OperEx(TlaActionOper.composition, OperEx(trueOper), OperEx(trueOper)))(mod.declarations(25))
    assertTlaDecl("Guarantees",
      OperEx(TlaTempOper.guarantees, OperEx(trueOper), OperEx(trueOper)))(mod.declarations(26))
    assertTlaDecl("Angleact",
      OperEx(TlaActionOper.nostutter, OperEx(trueOper), NameEx("x")))(mod.declarations(27))
    assertTlaDecl("BoundedChoose",
      OperEx(TlaOper.chooseBounded, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(28))
    assertTlaDecl("BoundedExists",
      OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(29))
    assertTlaDecl("BoundedForall",
      OperEx(TlaBoolOper.forall, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(30))
    assertTlaDecl("CartesianProd",
      OperEx(TlaSetOper.times, NameEx("x"), NameEx("x"), NameEx("x")))(mod.declarations(31))
    assertTlaDecl("Pair", OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2))))(mod.declarations(32))
    assertTlaDecl("Tuple",
      OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3))))(mod.declarations(33))
    assertTlaDecl("Case",
      OperEx(TlaControlOper.caseNoOther, 1.to(6).map(i => ValEx(TlaInt(i))): _*))(mod.declarations(34))
    assertTlaDecl("CaseOther",
      OperEx(TlaControlOper.caseWithOther, (7 +: 1.to(6)).map(i => ValEx(TlaInt(i))): _*))(mod.declarations(35))
    assertTlaDecl("ConjList",
      OperEx(TlaBoolOper.and, List(TlaFalse, TlaTrue, TlaFalse).map(b => ValEx(b)): _*))(mod.declarations(36))
    assertTlaDecl("DisjList",
      OperEx(TlaBoolOper.or, List(TlaFalse, TlaTrue, TlaFalse).map(b => ValEx(b)): _*))(mod.declarations(37))
    assertTlaDecl("Except",
      OperEx(TlaFunOper.except,
        NameEx("x"), TlaFunOper.mkTuple(ValEx(TlaInt(0))), ValEx(TlaInt(1))
      ))(mod.declarations(38))
    assertTlaDecl("FcnApply", OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(1))))(mod.declarations(39))
    val cup = OperEx(TlaSetOper.cup, NameEx("y"), NameEx("y"))
    assertTlaDecl("FcnCtor",
      OperEx(TlaFunOper.funDef, cup, NameEx("y"), NameEx("x")))(mod.declarations(40))
    assertTlaDecl("IfThenElse",
      OperEx(TlaControlOper.ifThenElse, ValEx(TlaTrue), ValEx(TlaFalse), ValEx(TlaTrue)))(mod.declarations(41))
    assertTlaDecl("RcdCtor",
      OperEx(TlaFunOper.enum,
        ValEx(TlaStr("a")), ValEx(TlaInt(1)), ValEx(TlaStr("b")), ValEx(TlaInt(2))))(mod.declarations(42))
    assertTlaDecl("RcdSelect",
      OperEx(TlaFunOper.app,
        NameEx("x"), ValEx(TlaStr("foo"))))(mod.declarations(43))
    assertTlaDecl("SetEnumerate",
      OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3))))(mod.declarations(44))
    assertTlaDecl("SetOfFcns", OperEx(TlaSetOper.funSet, NameEx("x"), NameEx("x")))(mod.declarations(45))
    assertTlaDecl("SetOfRcds",
      OperEx(TlaSetOper.recSet,
        ValEx(TlaStr("a")), NameEx("x"), ValEx(TlaStr("b")), NameEx("x")))(mod.declarations(46))
    assertTlaDecl("StrongFairness",
      OperEx(TlaTempOper.strongFairness, NameEx("x"), OperEx(trueOper)))(mod.declarations(47))
    assertTlaDecl("WeakFairness",
      OperEx(TlaTempOper.weakFairness, NameEx("x"), OperEx(trueOper)))(mod.declarations(48))
    assertTlaDecl("SquareAct",
      OperEx(TlaActionOper.stutter, OperEx(trueOper), NameEx("x")))(mod.declarations(49))
    assertTlaDecl("TemporalExists",
      OperEx(TlaTempOper.EE, NameEx("y"), OperEx(trueOper)))(mod.declarations(50))
    assertTlaDecl("TemporalForall",
      OperEx(TlaTempOper.AA, NameEx("y"), OperEx(trueOper)))(mod.declarations(51))
    assertTlaDecl("UnboundedChoose",
      OperEx(TlaOper.chooseUnbounded, NameEx("y"), ValEx(TlaTrue)))(mod.declarations(52))
    assertTlaDecl("UnboundedExists",
      OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaTrue)))(mod.declarations(53))
    assertTlaDecl("UnboundedForall",
      OperEx(TlaBoolOper.forallUnbounded, NameEx("y"), ValEx(TlaTrue)))(mod.declarations(54))
    assertTlaDecl("SetOfAll",
      OperEx(TlaSetOper.map, ValEx(TlaInt(1)), NameEx("y"), NameEx("x")))(mod.declarations(55))
    assertTlaDecl("SubsetOf",
      OperEx(TlaSetOper.filter, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(56))
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
    val mod = expectModule("composite", rootName, modules)

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
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue)))) (mod.declarations(2))
    assertTlaDecl("Q2",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue)))) (mod.declarations(3))
    assertTlaDecl("Q3",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
            ValEx(TlaTrue))))) (mod.declarations(4))
    assertTlaDecl("Q4",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")), NameEx("Z"),
            OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
              ValEx(TlaTrue)))))) (mod.declarations(5))
    assertTlaDecl("Q5",
      OperEx(TlaBoolOper.existsUnbounded, NameEx("x"),
        OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaTrue)))) (mod.declarations(6))
  }

  test("complex updates") {
    // One can write tricky combinations of EXCEPT arguments.
    val text =
      """---- MODULE updates ----
        |VARIABLE f
        |E1 == [ f EXCEPT ![0] = 1, ![2] = 3 ]
        |E2 == [ f EXCEPT ![0][1][2] = 3 ]
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("updates", Source.fromString(text))
    val mod = expectModule("updates", rootName, modules)

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
    val mod = expectModule("selects", rootName, modules)

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
    ) (mod.declarations(1))
    assertTlaDecl("S2",
      OperEx(TlaFunOper.app,
        OperEx(TlaFunOper.app,
          OperEx(TlaFunOper.app,
            NameEx("f"),
            ValEx(TlaStr("a"))),
          ValEx(TlaStr("b"))),
        ValEx(TlaStr("c")))
    ) (mod.declarations(2))
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
    val mod = expectModule("funCtor", rootName, modules)

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
        NameEx("y"), NameEx("X"))) (mod.declarations(2))
    assertTlaDecl("C2",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"))) (mod.declarations(3))
    assertTlaDecl("C3",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        NameEx("z"), NameEx("Z")
      )) (mod.declarations(4))
    assertTlaDecl("C4",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        TlaFunOper.mkTuple(NameEx("a"), NameEx("b")), NameEx("Z"),
        NameEx("z"), NameEx("Z")
      )) (mod.declarations(5))
  }

  test("level-1 operators") {
    // operators with basic parameters, that is, no operator is passed as a parameter
    val text =
    """---- MODULE level1Operators ----
      |VARIABLE x, y
      |A(i, j) == i \cup j
      |================================
      |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("level1Operators", Source.fromString(text))
    val mod = expectModule("level1Operators", rootName, modules)

    def assertTlaDecl(name: String, params: List[FormalParam], body: TlaEx): TlaDecl => Unit = {
      case d: TlaOperDecl =>
        assert(name == d.name)
        assert(params == d.formalParams)
        assert(body == d.body)

      case _ =>
        fail("Expected a TlaDecl")
    }

    assertTlaDecl("A", List(SimpleFormalParam("i"), SimpleFormalParam("j")),
      OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j"))) (mod.declarations(2))
  }

  test("level-2 operators") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE level2Operators ----
        |VARIABLE x, y
        |A(i, j, f(_)) == f(i \cup j)
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().load("level2Operators", Source.fromString(text))
    val mod = expectModule("level2Operators", rootName, modules)

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
      OperEx(new OperFormalParamOper(OperFormalParam("f", FixedArity(1))),
        OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j")))) (mod.declarations(2))
  }

  ////////////////////////////////////////////////////////////////////
  private def expectModule(expectedRootName: String, rootName: String, modules: Map[String, TlaModule]): TlaModule = {
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
