package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper, TlaSetOper}
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
    // following the operator table from tla2sany.semantic.BuiltInLevel.LevelData
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
        |================================
        |""".stripMargin

    //        |CartesianProd == ????????????
    //        |Case == ??????????
    //        |ConjList == /\ FALSE
    //        |            /\ TRUE
    //        |DisjList == \/ FALSE
    //        |            \/ TRUE
    //        |Except == [ x EXCEPT ![0] = 1 ]
    //        |FcnApply == x[0]
    //        |FcnConstructor == { y \in x |-> y }
    //        |IfThenElse == IF TRUE THEN FALSE ELSE TRUE
    //        |NonRecursiveFcnSpec == ??????????
    //        |Pair == <<1, 2>> ?????
    //        |RcdConstructor == { "a" |-> 1, "b" |-> 2 }
    //        |RcdSelect == x.foo
    //        |RecursiveFcnSpec == ????????
    //        |Seq == <<1, 2, 3>>
    //        |SetEnumerate == { 1, 2, 3 }
    //        |SetOfAll == ???
    //        |SetOfFcns == [ x -> x ]
    //        |SetOfRcds == { "a": x, "b": x }
    //        |StrongFairness == SF????
    //        |SquareAct == [True]_x
    //        |TemporalExists == \EE x???
    //        |TemporalForall == \AA x???
    //        |TemporalWhile == ????
    //        |Tuple == <<1, 2, 3>>
    //        |UnboundedChoose ==
    //        |UnboundedExists ==
    //        |UnboundedForall ==
    //        |WeakFairness == ...

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
    assertTlaDecl("Guarantees", OperEx(TlaTempOper.guarantees, OperEx(trueOper), OperEx(trueOper)))(mod.declarations(26))
    assertTlaDecl("Angleact", OperEx(TlaActionOper.nostutter, OperEx(trueOper), NameEx("x")))(mod.declarations(27))
    assertTlaDecl("BoundedChoose", OperEx(TlaOper.chooseBounded, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(28))
    assertTlaDecl("BoundedExists", OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(29))
    assertTlaDecl("BoundedForall", OperEx(TlaBoolOper.forall, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))(mod.declarations(30))
  }

  test("composite quantifiers") {
    // one can write tricky combinations of bound variables in TLA+
    val text =
      """---- MODULE composite ----
        |VARIABLE X, Z
        |Q1 == \E x \in X: \E y \in X: TRUE
        |Q2 == \E x, y \in X: TRUE
        |Q3 == \E x, y \in X, z \in Z: TRUE
        |Q4 == \E x, y \in X, <<a, b>> \in Z, z \in Z: TRUE
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
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue))))
      mod.declarations(1)
    assertTlaDecl("Q2",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue))))
      mod.declarations(2)
    assertTlaDecl("Q4",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
            ValEx(TlaTrue)))))
      mod.declarations(3)
    assertTlaDecl("Q4",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")), NameEx("Z"),
            OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
              ValEx(TlaTrue))))))
      mod.declarations(4)
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
