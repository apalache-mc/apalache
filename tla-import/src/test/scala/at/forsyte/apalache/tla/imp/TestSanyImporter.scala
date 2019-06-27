package at.forsyte.apalache.tla.imp

import java.io.{File, PrintWriter}
import java.nio.file.Files

import at.forsyte.apalache.tla.imp.src.{SourcePosition, SourceRegion, SourceStore}
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.control.{LetInOper, TlaControlOper}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.predef._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.{OperEx, ValEx, _}
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

  def expectTlaDecl(sourceStore: SourceStore, name: String, params: List[FormalParam],
                    body: TlaEx): (TlaDecl => Unit) = {
    case d: TlaOperDecl =>
      assert(name == d.name)
      assert(params == d.formalParams)
      assert(body == d.body)
      assert(sourceStore.contains(d.body.ID)) // and source file information has been saved

    case d@_ =>
      fail("Expected a TlaOperDecl, found: " + d)
  }

  def findAndExpectTlaDecl(sourceStore: SourceStore,
                           mod: TlaModule,
                           name: String,
                           params: List[FormalParam],
                           body: TlaEx): Unit = {
    mod.declarations.find {
      _.name == name
    } match {
      case Some(d: TlaOperDecl) =>
        expectTlaDecl(sourceStore, name, List(), body)

      case _ =>
        fail("Expected a TlaDecl")
    }
  }

  test("empty module") {
    val text =
      """---- MODULE justASimpleTest ----
        |================================
      """.stripMargin

    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromSource("justASimpleTest", Source.fromString(text))
    assert("justASimpleTest" == rootName)
  }

  test("empty module from a file") {
    val text =
      """---- MODULE justASimpleTest ----
        |================================
      """.stripMargin

    val tempDir = Files.createTempDirectory("sanyimp").toFile
    val temp = new File(tempDir, "justASimpleTest.tla")
    val source = Source.fromString(text)
    // write the contents to a temporary file
    val pw = new PrintWriter(temp)
    try {
      source.getLines().foreach(line => pw.println(line))
    } finally {
      pw.close()
    }

    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromFile(temp)
    assert("justASimpleTest" == rootName)
  }

  test("one variable") {
    val text =
      """---- MODULE onevar ----
        |VARIABLE x
        |================================
      """.stripMargin

    val (rootName, modules) =
      new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
        .loadFromSource("onevar", Source.fromString(text))
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

    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromSource("oneconst", Source.fromString(text))
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaInt(1)) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
      val loc = locationStore.find(actionDecl.body.ID).get
        assert(SourceRegion(SourcePosition(2, 9), SourcePosition(2, 9)) == loc.region)
    }
  }

  test("constant operator (decimal)") {
    val text =
      """---- MODULE constop ----
        |MyOp == 123.456
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaDecimal(BigDecimal("123.456"))) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
      val loc = locationStore.find(actionDecl.body.ID).get
        assert(SourceRegion(SourcePosition(2, 9), SourcePosition(2, 15)) == loc.region)
    }
  }

  test("constant operator (string)") {
    val text =
      """---- MODULE constop ----
        |MyOp == "Hello"
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaStr("Hello")) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
      val loc = locationStore.find(actionDecl.body.ID).get
        assert(SourceRegion(SourcePosition(2, 9), SourcePosition(2, 15)) == loc.region)
    }
  }

  test("constant operator (FALSE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == FALSE
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(false)) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
      val loc = locationStore.find(actionDecl.body.ID).get
        assert("constop" == loc.filename)
        assert(SourceRegion(SourcePosition(2, 9), SourcePosition(2, 13)) == loc.region)
    }
  }

  test("constant operator (TRUE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == TRUE
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(true)) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(2 == mod.declarations.size)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(NameEx("x") == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
      val loc = locationStore.find(actionDecl.body.ID).get
        assert(SourceRegion(SourcePosition(4, 9), SourcePosition(4, 9)) == loc.region)
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(2 == mod.declarations.size)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(NameEx("n") == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
    }
  }

  test("constant operator (a builtin operator)") {
    val text =
      """---- MODULE builtinop ----
        |MyOp == FALSE \/ TRUE
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("builtinop", Source.fromString(text))
    val mod = expectSingleModule("builtinop", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue)) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
      val loc = locationStore.find(actionDecl.body.ID).get
        assert(SourceRegion(SourcePosition(2, 9), SourcePosition(2, 21)) == loc.region)
    }
  }

  test("empty set") {
    val text =
      """---- MODULE emptyset ----
        |MyOp == {}
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("emptyset", Source.fromString(text))
    val mod = expectSingleModule("emptyset", rootName, modules)
    assert(1 == mod.declarations.size)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaSetOper.enumSet) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
    }
  }


  test("constant operator (a builtin op and variables)") {
    val text =
      """---- MODULE builtinop ----
        |VARIABLE x
        |MyOp == x /\ TRUE
        |================================
      """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("builtinop", Source.fromString(text))
    val mod = expectSingleModule("builtinop", rootName, modules)
    assert(2 == mod.declarations.size)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaBoolOper.and, NameEx("x"), ValEx(TlaTrue)) == actionDecl.body)
        assert(locationStore.contains(actionDecl.body.ID)) // and source file information has been saved
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
      |ExceptAt == [ x EXCEPT ![0] = @ /\ TRUE]
      |FcnApply == x[1]
      |FcnCtor == [ y \in x |-> y \cup y ]
      |FcnCtor2 == [ a \in x, b \in BOOLEAN |-> <<a, b>> ]
      |FcnCtor3 == [ <<a, b>> \in x \X BOOLEAN |-> <<a, b>> ]
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
      |SetOfTuples == { <<a, b>> : a \in x, b \in x }
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("builtins", Source.fromString(text))
    val mod = expectSingleModule("builtins", rootName, modules)
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    val trueOperDecl = mod.declarations(1)
    expectDecl("True", ValEx(TlaTrue))
    val trueOper = TlaOperDecl("True", List(), ValEx(TlaTrue)).operator
    assert(OperEx(trueOper) == OperEx(trueOper))

    expectDecl("Eq", OperEx(TlaOper.eq, ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("Ne", OperEx(TlaOper.ne, ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("Prime", OperEx(TlaActionOper.prime, NameEx("x")))
    expectDecl("Not", OperEx(TlaBoolOper.not, NameEx("x")))
    expectDecl("Or", OperEx(TlaBoolOper.or, ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("And", OperEx(TlaBoolOper.and, ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("Equiv", OperEx(TlaBoolOper.equiv, ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("Implies", OperEx(TlaBoolOper.implies, ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("Subset", OperEx(TlaSetOper.SUBSET, NameEx("x")))
    expectDecl("Union", OperEx(TlaSetOper.union, NameEx("x")))
    expectDecl("Domain", OperEx(TlaFunOper.domain, NameEx("x")))
    expectDecl("Subseteq", OperEx(TlaSetOper.subseteq, NameEx("x"), NameEx("x")))
    expectDecl("In", OperEx(TlaSetOper.in, NameEx("x"), NameEx("x")))
    expectDecl("Notin", OperEx(TlaSetOper.notin, NameEx("x"), NameEx("x")))
    expectDecl("Setminus", OperEx(TlaSetOper.setminus, NameEx("x"), NameEx("x")))
    expectDecl("Cap", OperEx(TlaSetOper.cap, NameEx("x"), NameEx("x")))
    expectDecl("Cup", OperEx(TlaSetOper.cup, NameEx("x"), NameEx("x")))
    expectDecl("Times", OperEx(TlaSetOper.times, NameEx("x"), NameEx("x")))
    expectDecl("LeadsTo", OperEx(TlaTempOper.leadsTo, ValEx(TlaTrue), ValEx(TlaTrue)))
    expectDecl("Box", OperEx(TlaTempOper.box, ValEx(TlaTrue)))
    expectDecl("Diamond", OperEx(TlaTempOper.diamond, ValEx(TlaTrue)))
    expectDecl("Enabled", OperEx(TlaActionOper.enabled, NameEx("x")))
    expectDecl("Unchanged", OperEx(TlaActionOper.unchanged, NameEx("x")))
    expectDecl("Cdot", OperEx(TlaActionOper.composition, OperEx(trueOper), OperEx(trueOper)))
    expectDecl("Guarantees",
      OperEx(TlaTempOper.guarantees, OperEx(trueOper), OperEx(trueOper)))
    expectDecl("Angleact",
      OperEx(TlaActionOper.nostutter, OperEx(trueOper), NameEx("x")))
    expectDecl("BoundedChoose",
      OperEx(TlaOper.chooseBounded, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    expectDecl("BoundedExists",
      OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    expectDecl("BoundedForall",
      OperEx(TlaBoolOper.forall, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    expectDecl("CartesianProd",
      OperEx(TlaSetOper.times, NameEx("x"), NameEx("x"), NameEx("x")))
    expectDecl("Pair", OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2))))
    expectDecl("Tuple",
      OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    expectDecl("Case",
      OperEx(TlaControlOper.caseNoOther, 1.to(6).map(i => ValEx(TlaInt(i))): _*))
    expectDecl("CaseOther",
      OperEx(TlaControlOper.caseWithOther, (7 +: 1.to(6)).map(i => ValEx(TlaInt(i))): _*))
    expectDecl("ConjList",
      OperEx(TlaBoolOper.and, List(TlaFalse, TlaTrue, TlaFalse).map(b => ValEx(b)): _*))
    expectDecl("DisjList",
      OperEx(TlaBoolOper.or, List(TlaFalse, TlaTrue, TlaFalse).map(b => ValEx(b)): _*))
    expectDecl("Except",
      OperEx(TlaFunOper.except,
        NameEx("x"), TlaFunOper.mkTuple(ValEx(TlaInt(0))), ValEx(TlaInt(1))
      ))
    expectDecl("ExceptAt",
      OperEx(TlaFunOper.except,
        NameEx("x"),
        TlaFunOper.mkTuple(ValEx(TlaInt(0))),
        OperEx(TlaBoolOper.and,
          OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(0))),
          ValEx(TlaTrue))
      ))
    expectDecl("FcnApply", OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(1))))
    val cup = OperEx(TlaSetOper.cup, NameEx("y"), NameEx("y"))
    expectDecl("FcnCtor",
      OperEx(TlaFunOper.funDef, cup, NameEx("y"), NameEx("x")))
    expectDecl("FcnCtor2",
      OperEx(TlaFunOper.funDef, OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
        NameEx("a"), NameEx("x"), NameEx("b"), NameEx("x")))
    expectDecl("FcnCtor3",
      OperEx(TlaFunOper.funDef, OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
        OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")), NameEx("x")))
    expectDecl("IfThenElse",
      OperEx(TlaControlOper.ifThenElse, ValEx(TlaTrue), ValEx(TlaFalse), ValEx(TlaTrue)))
    expectDecl("RcdCtor",
      OperEx(TlaFunOper.enum,
        ValEx(TlaStr("a")), ValEx(TlaInt(1)), ValEx(TlaStr("b")), ValEx(TlaInt(2))))
    expectDecl("RcdSelect",
      OperEx(TlaFunOper.app,
        NameEx("x"), ValEx(TlaStr("foo"))))
    expectDecl("SetEnumerate",
      OperEx(TlaSetOper.enumSet, ValEx(TlaInt(1)), ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    expectDecl("SetOfFcns", OperEx(TlaSetOper.funSet, NameEx("x"), NameEx("x")))
    expectDecl("SetOfRcds",
      OperEx(TlaSetOper.recSet,
        ValEx(TlaStr("a")), NameEx("x"), ValEx(TlaStr("b")), NameEx("x")))
    expectDecl("StrongFairness",
      OperEx(TlaTempOper.strongFairness, NameEx("x"), OperEx(trueOper)))
    expectDecl("WeakFairness",
      OperEx(TlaTempOper.weakFairness, NameEx("x"), OperEx(trueOper)))
    expectDecl("SquareAct",
      OperEx(TlaActionOper.stutter, OperEx(trueOper), NameEx("x")))
    expectDecl("TemporalExists",
      OperEx(TlaTempOper.EE, NameEx("y"), OperEx(trueOper)))
    expectDecl("TemporalForall",
      OperEx(TlaTempOper.AA, NameEx("y"), OperEx(trueOper)))
    expectDecl("UnboundedChoose",
      OperEx(TlaOper.chooseUnbounded, NameEx("y"), ValEx(TlaTrue)))
    expectDecl("UnboundedExists",
      OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaTrue)))
    expectDecl("UnboundedForall",
      OperEx(TlaBoolOper.forallUnbounded, NameEx("y"), ValEx(TlaTrue)))
    expectDecl("SetOfAll",
      OperEx(TlaSetOper.map, ValEx(TlaInt(1)), NameEx("y"), NameEx("x")))
    expectDecl("SetOfTuples",
      OperEx(TlaSetOper.map, OperEx(TlaFunOper.tuple), NameEx("a"), NameEx("x"), NameEx("b"), NameEx("x")))
    expectDecl("SubsetOf",
      OperEx(TlaSetOper.filter, NameEx("y"), NameEx("x"), ValEx(TlaTrue)))
    expectDecl("Boolean", ValEx(TlaBoolSet))
    expectDecl("String", ValEx(TlaStrSet))
  }

  test("comprehensions with tuples") {
    // TLA+ allows the user to use some form of pattern matching with tuples
    val text =
    """---- MODULE comprehensions ----
      |VARIABLE XY, X, Y
      |FilterTuples == { <<x, y>> \in XY :  x = 1}
      |MapTuples == { x = 1 : <<x, y>> \in XY}
      |MapTuples2 == { x = 1 : x, y \in XY}
      |================================
      |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("comprehensions", Source.fromString(text))
    val mod = expectSingleModule("comprehensions", rootName, modules)
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    expectDecl("FilterTuples",
      OperEx(TlaSetOper.filter,
        OperEx(TlaFunOper.tuple, NameEx("x"), NameEx("y")),
        NameEx("XY"),
        OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(1)))
      ))////
    expectDecl("MapTuples",
      OperEx(TlaSetOper.map,
        OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(1))),
        OperEx(TlaFunOper.tuple, NameEx("x"), NameEx("y")),
        NameEx("XY")
      ))////
    expectDecl("MapTuples2",
      OperEx(TlaSetOper.map,
        OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(1))),
        OperEx(TlaFunOper.tuple, NameEx("x"), NameEx("y")),
        NameEx("XY")
      ))////
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("composite", Source.fromString(text))
    val mod = expectSingleModule("composite", rootName, modules)

    def expectDecl(name: String, body: TlaEx): (TlaDecl => Unit) =
      expectTlaDecl(locationStore, name, List(), body)

    expectDecl("Q1",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue))))(mod.declarations(2))
    expectDecl("Q2",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"), ValEx(TlaTrue))))(mod.declarations(3))
    expectDecl("Q3",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
            ValEx(TlaTrue)))))(mod.declarations(4))
    expectDecl("Q4",
      OperEx(TlaBoolOper.exists, NameEx("x"), NameEx("X"),
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("X"),
          OperEx(TlaBoolOper.exists, OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")), NameEx("Z"),
            OperEx(TlaBoolOper.exists, NameEx("z"), NameEx("Z"),
              ValEx(TlaTrue))))))(mod.declarations(5))
    expectDecl("Q5",
      OperEx(TlaBoolOper.existsUnbounded, NameEx("x"),
        OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaTrue))))(mod.declarations(6))
  }

  test("function updates") {
    val text =
      """---- MODULE except ----
        |VARIABLE x
        |Except == [ x EXCEPT ![0] = 1 ]
        |ExceptAt == [ x EXCEPT ![0] = @ /\ TRUE]
        |ExceptTuple == [ x EXCEPT ![<<0>>] = 1 ]
        |ExceptManyAt == [ x EXCEPT ![1][2] = @ /\ TRUE]
        |================================
        |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("except", Source.fromString(text))
    val mod = expectSingleModule("except", rootName, modules)

    def expectDecl(name: String, params: List[FormalParam], body: TlaEx) = expectTlaDecl(locationStore, name, params, body)

    expectDecl("Except",
      List(),
      OperEx(TlaFunOper.except,
        NameEx("x"), TlaFunOper.mkTuple(ValEx(TlaInt(0))), ValEx(TlaInt(1))
      ))(mod.declarations(1))

    expectDecl("ExceptAt",
      List(),
      OperEx(TlaFunOper.except,
        NameEx("x"),
        TlaFunOper.mkTuple(ValEx(TlaInt(0))),
        OperEx(TlaBoolOper.and,
          OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(0))),
          ValEx(TlaTrue))
      ))(mod.declarations(2))

    expectDecl("ExceptTuple",
      List(),
      OperEx(TlaFunOper.except,
        NameEx("x"), TlaFunOper.mkTuple(TlaFunOper.mkTuple(ValEx(TlaInt(0)))), ValEx(TlaInt(1))
      ))(mod.declarations(3))

    // the importer automatically substitutes @ with function application and unfolds ![1][2] to a chain of EXCEPTS
    expectDecl("ExceptManyAt",
      List(),
      OperEx(TlaFunOper.except,
        NameEx("x"),
        TlaFunOper.mkTuple(ValEx(TlaInt(1))),
        OperEx(TlaFunOper.except,
          OperEx(TlaFunOper.app,
            NameEx("x"),
            ValEx(TlaInt(1))),
          TlaFunOper.mkTuple(ValEx(TlaInt(2))),
          OperEx(TlaBoolOper.and,
            OperEx(TlaFunOper.app,
              OperEx(TlaFunOper.app,
                NameEx("x"), ValEx(TlaInt(1))),
              ValEx(TlaInt(2))
            ), ///
            ValEx(TlaTrue))
        )))(mod.declarations(4))
  }

  test("expression labels") {
    val text =
      """---- MODULE labels ----
        |A == {FALSE} \cup (l1 :: {TRUE})
        |B == \E x \in BOOLEAN: l2(x) :: x /= FALSE
        |================================
        |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("labels", Source.fromString(text))
    val mod = expectSingleModule("labels", rootName, modules)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) = expectTlaDecl(locationStore, n, p, b)

    //    A == {FALSE} \cup (l1 :: {TRUE})
    val expectedABody =
      OperEx(TlaSetOper.cup,
        OperEx(TlaSetOper.enumSet, ValEx(TlaBool(false))),
        OperEx(TlaOper.label,
          OperEx(TlaSetOper.enumSet, ValEx(TlaBool(true))),
          ValEx(TlaStr("l1")))) ////
    expectDecl("A", List(), expectedABody)(mod.declarations.head)

    //    B == \E x \in BOOLEAN: l2(x) :: x /= FALSE
    // since we cannot access formal parameters, we ignore them
    val expectedBBody =
    OperEx(TlaBoolOper.exists,
      NameEx("x"),
      ValEx(TlaBoolSet),
      OperEx(TlaOper.label,
        OperEx(TlaOper.ne, NameEx("x"), ValEx(TlaBool(false))),
        ValEx(TlaStr("l2")))) ////
    expectDecl("B", List(), expectedBBody)(mod.declarations.tail.head)
  }

  test("tuples as arguments") {
    // test that single function arguments are translated consistently
    val text =
      """---- MODULE args ----
        |VARIABLE f, g, e, h
        |
        |A == f[2]
        |B == g["green"]
        |C == e[FALSE]
        |D == h[{}]
        |================================
        |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("args", Source.fromString(text))
    val mod = expectSingleModule("args", rootName, modules)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) = expectTlaDecl(locationStore, n, p, b)

    val expectedABody = OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaInt(2)))
    expectDecl("A", List(), expectedABody)(mod.declarations(4))

    val expectedBBody = OperEx(TlaFunOper.app, NameEx("g"), ValEx(TlaStr("green")))
    expectDecl("B", List(), expectedBBody)(mod.declarations(5))

    val expectedCBody = OperEx(TlaFunOper.app, NameEx("e"), ValEx(TlaBool(false)))
    expectDecl("C", List(), expectedCBody)(mod.declarations(6))

    val expectedDBody = OperEx(TlaFunOper.app, NameEx("h"), OperEx(TlaSetOper.enumSet))
    expectDecl("D", List(), expectedDBody)(mod.declarations(7))
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("updates", Source.fromString(text))
    val mod = expectSingleModule("updates", rootName, modules)

    def expectDecl(name: String, body: TlaEx): (TlaDecl => Unit) =
      expectTlaDecl(locationStore, name, List(), body)

    expectDecl("E1",
      OperEx(TlaFunOper.except,
        NameEx("f"),
        TlaFunOper.mkTuple(ValEx(TlaInt(0))), ValEx(TlaInt(1)),
        TlaFunOper.mkTuple(ValEx(TlaInt(2))), ValEx(TlaInt(3))
      ))(mod.declarations(1))
    expectDecl("E2",
      OperEx(TlaFunOper.except,
        NameEx("f"),
        TlaFunOper.mkTuple(ValEx(TlaInt(0))),
        OperEx(TlaFunOper.except,
          OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaInt(0))),
          TlaFunOper.mkTuple(ValEx(TlaInt(1))),
          OperEx(TlaFunOper.except,
            OperEx(TlaFunOper.app, OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaInt(0))), ValEx(TlaInt(1))),
            TlaFunOper.mkTuple(ValEx(TlaInt(2))),
            ValEx(TlaInt(3)))
        )//
      ))(mod.declarations(2))
    expectDecl("E3",
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("selects", Source.fromString(text))
    val mod = expectSingleModule("selects", rootName, modules)

    def expectDecl(name: String, body: TlaEx): (TlaDecl => Unit) =
      expectTlaDecl(locationStore, name, List(), body)

    expectDecl("S1",
      OperEx(TlaFunOper.app,
        OperEx(TlaFunOper.app,
          NameEx("f"),
          ValEx(TlaStr("a"))),
        ValEx(TlaStr("b")))
    )(mod.declarations(1))
    expectDecl("S2",
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("funCtor", Source.fromString(text))
    val mod = expectSingleModule("funCtor", rootName, modules)

    def expectDecl(name: String, body: TlaEx) = expectTlaDecl(locationStore, name, List(), body)

    expectDecl("C1",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X")))(mod.declarations(2))
    expectDecl("C2",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X")))(mod.declarations(3))
    expectDecl("C3",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        NameEx("z"), NameEx("Z")
      ))(mod.declarations(4))
    expectDecl("C4",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaTrue),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        NameEx("a_b"), NameEx("Z"), // the tuple <<a, b>> is collapsed to a_b by Desugarer
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("level1Operators", Source.fromString(text))
    val mod = expectSingleModule("level1Operators", rootName, modules)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) = expectTlaDecl(locationStore, n, p, b)

    expectDecl("A", List(SimpleFormalParam("i"), SimpleFormalParam("j")),
      OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j")))(mod.declarations(2))
    expectDecl("**", List(SimpleFormalParam("i"), SimpleFormalParam("j")),
      OperEx(TlaSetOper.cap, NameEx("i"), NameEx("j")))(mod.declarations(3))
    val aDecl = mod.declarations(2).asInstanceOf[TlaOperDecl]
    expectDecl("C", List(),
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("level2Operators", Source.fromString(text))
    val mod = expectSingleModule("level2Operators", rootName, modules)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) = expectTlaDecl(locationStore, n, p, b)

    expectDecl("A",
      List(SimpleFormalParam("i"), SimpleFormalParam("j"), OperFormalParam("f", FixedArity(1))),
      OperEx(TlaOper.apply, NameEx("f"),
        OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j"))))(mod.declarations(2))
    val aDecl = mod.declarations(2).asInstanceOf[TlaOperDecl]
    expectDecl("C", List(),
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("let", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find {
      _.name == "A"
    } match {
      case Some(TlaOperDecl(_, _, OperEx(o: LetInOper, body))) =>
        assert(3 == o.defs.length)
        val xDecl = o.defs.head
        assert("X" == xDecl.name)
        val yDecl = o.defs(1)
        assert(TlaOperDecl("Y",
          List(SimpleFormalParam("a")),
          NameEx("a")) == yDecl)
        assert(locationStore.contains(yDecl.body.ID)) // and source file information has been saved

        val zDecl = o.defs(2)
        zDecl match {
          case TlaOperDecl("Z", List(OperFormalParam("f", FixedArity(1)), SimpleFormalParam("a")), _) =>
            assert(OperEx(TlaOper.apply, NameEx("f"), NameEx("a")) == zDecl.body)
        }
        assert(locationStore.contains(zDecl.body.ID)) // and source file information has been saved
        assert(0 == xDecl.formalParams.length)
        assert(ValEx(TlaInt(1)) == xDecl.body)
        // although "X" might seem to be a variable, it is actually an operator without any arguments
        assert(OperEx(xDecl.operator) == body)
        assert(locationStore.contains(xDecl.body.ID)) // and source file information has been saved
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("let", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find {
      _.name == "A"
    } match {
      case Some(TlaOperDecl(_, _, OperEx(o: LetInOper, body))) =>
        assert(2 == o.defs.length)
        val fDecl = o.defs.head
        assert("f" == fDecl.name)
        val expectedBody =
          OperEx(TlaFunOper.funDef,
            OperEx(TlaFunOper.app,
              OperEx(TlaOper.apply, NameEx("f")),
              NameEx("x")),
            NameEx("x"),
            ValEx(TlaBoolSet)
          )

        assert(expectedBody == fDecl.body)
        assert(locationStore.contains(fDecl.body.ID)) // and source file information has been saved

        val xDecl = o.defs(1)
        assert("X" == xDecl.name)
        assert(OperEx(TlaOper.apply, NameEx("X")) == xDecl.body)
        assert(OperEx(xDecl.operator) == body)
        assert(locationStore.contains(xDecl.body.ID)) // and source file information has been saved
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("recOpers", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def assertRec(name: String, nparams: Int, expectedBody: TlaEx) = {
      root.declarations.find {
        _.name == name
      } match {
        case Some(d: TlaOperDecl) =>
          // We expect that R in the declaration body is referred by a formal parameter with the same name R.
          // The caveat here is that the formal parameter R does not appear in the list of the R's formal parameters,
          // but it is accessible via the field recParam.
          assert(d.isRecursive)
          val recParam = OperFormalParam(name, FixedArity(nparams))
          assert(d.body == expectedBody)
          assert(locationStore.contains(d.body.ID)) // and source file information has been saved

        case _ =>
          fail("expected TlaRecOperDecl")
      }
    }

    // in the recursive sections, the calls to recursive operators should be replaced with OperFormalParam(...)
    assertRec("R", 1,
      OperEx(TlaOper.apply, NameEx("R"), NameEx("n")))

    assertRec("A", 1,
      OperEx(TlaOper.apply, NameEx("B"), NameEx("n")))
    assertRec("B", 1,
      OperEx(TlaOper.apply, NameEx("C"), NameEx("n")))
    assertRec("C", 1,
      OperEx(TlaOper.apply, NameEx("A"), NameEx("n")))

    assertRec("X", 0,
      OperEx(TlaOper.apply, NameEx("X")))

    // however, in non-recursive sections, the calls to recursive operators are just normal OperEx(operator, ...)
    root.declarations.find {
      _.name == "D"
    } match {
      case Some(d: TlaOperDecl) =>
        val A = root.declarations.find {
          _.name == "A"
        }.get.asInstanceOf[TlaOperDecl]
        assert(OperEx(A.operator, NameEx("n")) == d.body)
        assert(locationStore.contains(d.body.ID)) // and source file information has been saved

      case _ =>
        fail("Expected TlaOperDecl")
    }

    // of course, we want to see the factorial
    root.declarations.find {
      _.name == "F"
    } match {
      case Some(d: TlaOperDecl) =>
        // We expect that F in the declaration body is referred by a formal parameter with the same name F.
        // The caveat here is that the formal parameter F does not appear in the list of the F's formal parameters,
        // but it is accessible via the field recParam.
        assert(d.isRecursive)
        val recParam = OperFormalParam("F", FixedArity(1))
        val ite = OperEx(TlaControlOper.ifThenElse,
          OperEx(TlaOper.eq, NameEx("n"), ValEx(TlaInt(0))),
          ValEx(TlaInt(1)),
          OperEx(TlaArithOper.mult, NameEx("n"),
            OperEx(TlaOper.apply, NameEx("F"), OperEx(TlaArithOper.minus, NameEx("n"), ValEx(TlaInt(1)))))
        )
        assert(d.body == ite)
        assert(locationStore.contains(d.body.ID)) // and source file information has been saved

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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("globalFuns", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // a non-recursive function becomes a nullary operator that always returns an equivalent function
    expectDecl("nonRecFun",
      OperEx(TlaFunOper.funDef, NameEx("x"), NameEx("x"), NameEx("S"))
    ) ///

    // a recursive function becomes a recursive nullary operator
    // that returns a function defined w.r.t. the recursive operator

    def assertTlaRecDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find {
        _.name == expectedName
      } match {
        case Some(d: TlaOperDecl) =>
          assert(d.isRecursive)
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)
          assert(locationStore.contains(d.body.ID)) // and source file information has been saved

        case _ =>
          fail("Expected a TlaRecDecl")
      }
    }

    assertTlaRecDecl("recFun",
      OperEx(TlaFunOper.funDef,
        OperEx(TlaFunOper.app,
          OperEx(TlaOper.apply, NameEx("recFun")),
          NameEx("x")),
        NameEx("x"),
        NameEx("S"))
    ) ///
  }

  test("instances") {
    val text =
      """---- MODULE inst ----
        |---- MODULE A ----
        |EXTENDS Naturals
        |CONSTANT N
        |F(x) == x + N
        |G == F(3)
        |================================
        |CONSTANT M
        |J == INSTANCE A WITH N <- M
        |\* I(V, K) == INSTANCE A WITH N <- K
        |---- MODULE B ----
        |---- MODULE C ----
        |H(x) == x
        |================================
        |CONSTANT M
        |C2 == INSTANCE C
        |F(x) == C2!H(x)
        |================================
        |B2 == INSTANCE B
        |================================
        |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("inst", Source.fromString(text))
    assert(2 == modules.size) // inst + Naturals
    // the root module and A
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find { _.name == "J!F" } match {
      case Some(TlaOperDecl(_, params,
          OperEx(TlaArithOper.plus, NameEx("x"), NameEx("M")))) =>
        assert(params.length == 1)
        assert(params.head.isInstanceOf[SimpleFormalParam])
        assert("x" == params.head.asInstanceOf[SimpleFormalParam].name)

      case _ =>
        fail("expected the body for J!F")
    }
    val fDecl = root.declarations.find { _.name == "J!F" }.get
    root.declarations.find { _.name == "J!G" } match {
      case Some(TlaOperDecl(_, params, body)) =>
        assert(params.isEmpty)
        assert(body == OperEx(new TlaUserOper("J!F", FixedArity(1), fDecl.asInstanceOf[TlaOperDecl]),
          ValEx(TlaInt(3))
        ))

      case _ =>
        fail("expected the body for J!G")
    }
    // an instance with parameters, not working yet
    /*
    root.declarations.find { _.name == "I!F" } match {
      case Some(TlaOperDecl(_, params,
          OperEx(TlaArithOper.plus, NameEx("x"), NameEx("K")))) =>
        assert(params.length == 3)
        assert(params.head == SimpleFormalParam("V"))
        assert(params(1) == SimpleFormalParam("K"))
        assert(params(2) == SimpleFormalParam("x"))

      case _ =>
        fail("expected the body for I!F")
    }
    */
    // two instances
    root.declarations.find { _.name == "B2!C2!H" } match {
      case Some(TlaOperDecl(_, params, NameEx("x"))) =>
        assert(params.length == 1)
        assert(params.head == SimpleFormalParam("x"))

      case _ =>
        fail("expected the body for B2!C2!H")
    }
  }

  test("module imports") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE imports ----
        |EXTENDS Naturals
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromSource("imports", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    // we strip away the operator declarations by Naturals
    assert(root.declarations.isEmpty)
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("nats", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // the root module contains its own declarations and the declarations by Naturals
    expectDecl("NatSet", ValEx(TlaNatSet))
    expectDecl("Plus", OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Minus", OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Mult", OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Power", OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Less", OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Greater", OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Leq", OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Geq", OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Mod", OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Div", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Range", OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))))

    // check the source info
    val plus = root.declarations.find {
      _.name == "Plus"
    } match {
      case Some(TlaOperDecl(_, _, oe@OperEx(oper, _*))) =>
        val loc = locationStore.find(oe.ID).get
        assert(SourceRegion(SourcePosition(4, 9), SourcePosition(4, 13)) == loc.region)

      case _ => fail()
    }
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("ints", Source.fromString(text))
    assert(3 == modules.size) // Integers extends Naturals
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(13 == root.declarations.size)

    // the root module contains its own declarations and the declarations by Integers
    expectDecl("IntSet", ValEx(TlaIntSet))
    expectDecl("Plus", OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Minus", OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Mult", OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Power", OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Less", OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Greater", OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Leq", OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Geq", OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Mod", OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Div", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Range", OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    expectDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("reals", Source.fromString(text))
    assert(4 == modules.size) // Reals include Integers that include Naturals
    val root = modules(rootName)
    // the definitions of the standard operators are filtered out
    assert(15 == root.declarations.size)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    expectDecl("RealSet", ValEx(TlaRealSet))
    expectDecl("Inf", ValEx(TlaRealInfinity))
    expectDecl("Plus", OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Minus", OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Mult", OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Power", OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Less", OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Greater", OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Leq", OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Geq", OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Mod", OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Div", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
    expectDecl("Range", OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3))))
    expectDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
    expectDecl("RealDiv", OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2))))
  }

  test("module seqs") {
    // check that the Sequences module is imported properly
    val text =
      """---- MODULE sequences ----
        |EXTENDS Sequences
        |
        |Empty == <<>>
        |Three == <<1, 2, 3>>
        |ASeq == Seq({1 , 2})
        |ALen == Len(<<1, 2, 3>>)
        |AConcat == <<1, 2>> \o <<3>>
        |AAppend == Append(<<1, 2>>, 3)
        |AHead == Head(<<1, 2, 3>>)
        |ATail == Tail(<<1, 2, 3>>)
        |ASubSeq == SubSeq(<<1, 2, 3, 4>>, 2, 3)
        |Test(i) == i = 2
        |ASelectSeq == SelectSeq(<<1, 2, 3, 4>>, Test)
        |================================
        |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("sequences", Source.fromString(text))
    assert(3 == modules.size) // Naturals, Sequences, and our module
    // the root module and naturals
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(11 == root.declarations.size)

    expectDecl("Empty", tla.tuple())
    expectDecl("Three", tla.tuple(tla.int(1), tla.int(2), tla.int(3)))
    expectDecl("ASeq", tla.seqSet(tla.enumSet(tla.int(1), tla.int(2))))
    expectDecl("ALen", tla.len(tla.tuple(tla.int(1), tla.int(2), tla.int(3))))
    expectDecl("AConcat",
      tla.concat(tla.tuple(tla.int(1), tla.int(2)),
        tla.tuple(tla.int(3))))
    expectDecl("AAppend",
      tla.append(tla.tuple(tla.int(1), tla.int(2)),
        tla.int(3)))
    expectDecl("AHead", tla.head(tla.tuple(tla.int(1), tla.int(2), tla.int(3))))
    expectDecl("ATail", tla.tail(tla.tuple(tla.int(1), tla.int(2), tla.int(3))))
    expectDecl("ASubSeq",
      tla.subseq(tla.tuple(tla.int(1), tla.int(2), tla.int(3), tla.int(4)),
        tla.int(2), tla.int(3)))
    expectDecl("ASelectSeq",
      tla.selectseq(tla.tuple(tla.int(1), tla.int(2), tla.int(3), tla.int(4)),
        tla.name("Test")))
  }

  // FiniteSets
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

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("finitesets", Source.fromString(text))
    assert(4 == modules.size) // Naturals, Sequences, FiniteSets, and our module
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(2 == root.declarations.size)

    // the root module contains its own declarations and the declarations by FiniteSets
    expectDecl("IsFinSet",
      OperEx(TlaFiniteSetOper.isFiniteSet, ValEx(TlaBoolSet)))
    expectDecl("Card",
      OperEx(TlaFiniteSetOper.cardinality, ValEx(TlaBoolSet)))
  }

  test("module TLC") {
    // check that the module TLC is imported properly
    val text =
      """---- MODULE tlc ----
        |EXTENDS TLC
        |
        |VARIABLES i
        |
        |APrint == Print("TLC Print", TRUE)
        |APrintT == PrintT("TLC PrintT")
        |AAssert == Assert("TLC Assert", TRUE)
        |AJavaTime == JavaTime
        |ATLCGet == TLCGet(i)
        |ATLCSet == TLCSet(i, 3)
        |AColonGreater == {1, 2} :> 3
        |AtAt == [j \in {1, 2} |-> j] @@ [k \in {3, 4} |-> k]
        |APermutations == Permutations(<<1, 2>>)
        |FakeSort(a, b) == TRUE
        |ASortSeq == SortSeq(<<2, 1>>, FakeSort)
        |ARandomElement == RandomElement({1, 2})
        |AAny == Any
        |AToString == ToString(42)
        |ATLCEval == TLCEval(42)
        |================================
        |""".stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("tlc", Source.fromString(text))
    assert(5 == modules.size) // our module + 4 LOCAL modules
    // the root module and naturals
    val root = modules(rootName)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectTlaDecl(locationStore, root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(16 == root.declarations.size)

    expectDecl("APrint",
      OperEx(TlcOper.print, tla.str("TLC Print"), tla.bool(true)))
    expectDecl("APrintT",
      OperEx(TlcOper.printT, tla.str("TLC PrintT")))
    expectDecl("AAssert",
      OperEx(TlcOper.assert, tla.str("TLC Assert"), tla.bool(true)))
    expectDecl("AJavaTime", OperEx(TlcOper.javaTime))
    expectDecl("ATLCGet",
      OperEx(TlcOper.tlcGet, tla.name("i")))
    expectDecl("ATLCSet",
      OperEx(TlcOper.tlcSet, tla.name("i"), tla.int(3)))
    expectDecl("AColonGreater",
      OperEx(TlcOper.colonGreater, tla.enumSet(tla.int(1), tla.int(2)), tla.int(3)))
    val fun12 = tla.funDef(tla.name("j"), tla.name("j"), tla.enumSet(tla.int(1), tla.int(2)))
    val fun34 = tla.funDef(tla.name("k"), tla.name("k"), tla.enumSet(tla.int(3), tla.int(4)))
    expectDecl("AtAt",
      OperEx(TlcOper.atat, fun12, fun34))
    expectDecl("APermutations",
      OperEx(TlcOper.permutations, tla.tuple(tla.int(1), tla.int(2))))
    expectDecl("ASortSeq",
      OperEx(TlcOper.sortSeq,
        tla.tuple(tla.int(2), tla.int(1)),
        tla.name("FakeSort")
      ))
    expectDecl("ARandomElement",
      OperEx(TlcOper.randomElement, tla.enumSet(tla.int(1), tla.int(2))))
    expectDecl("AAny", OperEx(TlcOper.any))
    expectDecl("ATLCEval", OperEx(TlcOper.tlcEval, tla.int(42)))
    expectDecl("AToString", OperEx(TlcOper.tlcToString, tla.int(42)))
  }

  test("type annotations (our custom extension)") {
    // This is a temporary solution until Jure write a proper type inference engine.
    // The operator <: should be defined somehow. We will rewrite it during the import phase.
    // It may look strange that we use sets (Int, BOOLEAN, Int, [A -> B]) to denote types,
    // but this solution is quite convenient and natural for TLA+.
    val text =
    """---- MODULE types ----
      |EXTENDS Integers
      |VARIABLE x, f
      |a <: b == a
      |SetOfInts == {} <: {Int}
      |SetOfBools == {} <: {BOOLEAN}
      |SetOfStrings == {} <: {STRING}
      |SetOfSetsOfInts == {} <: {{Int}}
      |Integer == 1 <: Int
      |Bool == FALSE <: BOOLEAN
      |Str == "a" <: STRING
      |Fun == f <: [Int -> Int]
      |SetOfFuns == f <: {[Int -> Int]}
      |Rec == f <: [a |-> Int, b |-> BOOLEAN]
      |SetOfRecs == {} <: {[a |-> Int, b |-> BOOLEAN]}
      |Tup == f <: <<Int, BOOLEAN>>
      |SetOfTuples == {} <: {<<Int, BOOLEAN>>}
      |================================
    """.stripMargin

    val locationStore = new SourceStore
    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, locationStore)
      .loadFromSource("types", Source.fromString(text))
    assert(3 == modules.size) // our module + Integers & Naturals
    val rootMod = modules("types")

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectTlaDecl(locationStore, rootMod, name, List(), body)

    expectDecl("SetOfInts",
      OperEx(BmcOper.withType, tla.enumSet(), tla.enumSet(ValEx(TlaIntSet))))

    expectDecl("SetOfBools",
      OperEx(BmcOper.withType, tla.enumSet(), tla.enumSet(ValEx(TlaBoolSet))))

    expectDecl("SetOfStrings",
      OperEx(BmcOper.withType, tla.enumSet(), tla.enumSet(ValEx(TlaStrSet))))

    expectDecl("SetOfInts",
      OperEx(BmcOper.withType, tla.enumSet(), tla.enumSet(ValEx(TlaIntSet))))

    expectDecl("SetOfSetsOfInts",
      OperEx(BmcOper.withType, tla.enumSet(), tla.enumSet(tla.enumSet(ValEx(TlaIntSet)))))

    expectDecl("Integer",
      OperEx(BmcOper.withType, tla.int(1), ValEx(TlaIntSet)))

    expectDecl("Bool",
      OperEx(BmcOper.withType, tla.bool(false), ValEx(TlaBoolSet)))

    expectDecl("Str",
      OperEx(BmcOper.withType, tla.str("a"), ValEx(TlaStrSet)))

    expectDecl("Fun",
      OperEx(BmcOper.withType, NameEx("f"), tla.funSet(ValEx(TlaIntSet), ValEx(TlaIntSet))))

    expectDecl("Rec",
      OperEx(BmcOper.withType, NameEx("f"),
        tla.enumFun(tla.str("a"), ValEx(TlaIntSet), tla.str("b"), ValEx(TlaBoolSet))))

    expectDecl("SetOfRecs",
      OperEx(BmcOper.withType, tla.enumSet(),
        tla.enumSet(tla.enumFun(tla.str("a"), ValEx(TlaIntSet), tla.str("b"), ValEx(TlaBoolSet)))))

    expectDecl("Tup",
      OperEx(BmcOper.withType, NameEx("f"),
        tla.tuple(ValEx(TlaIntSet), ValEx(TlaBoolSet))))

    expectDecl("SetOfTuples",
      OperEx(BmcOper.withType, tla.enumSet(),
        tla.enumSet(tla.tuple(ValEx(TlaIntSet), ValEx(TlaBoolSet)))))
  }


  /*
  TODO: we need a good way to propagate this module to the standard library

  test("module BMC") {
    // check that the module BMC is imported properly
    val text =
      """---- MODULE bmc ----
        |EXTENDS BMC
        |
        |VARIABLES i
        |
        |AWithType == WithType(i, "IntT")
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter().loadFromSource("bmc", Source.fromString(text))
    assert(2 == modules.size) // our module
    // the root module and naturals
    val root = modules(rootName)

    def assertTlaDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find {
        _.name == expectedName
      } match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(0 == d.formalParams.length)
          assert(body == d.body)

        case _ =>
          fail("Expected a TlaDecl")
      }
    }

    assertTlaDecl("AWithType",
      OperEx(BmcOper.withType, tla.name("i"), tla.str("IntT")))
  }
  */

  test("assumptions") {
    // this proof is a garbage, just to check, whether the translator works
    val text =
      """
        |---- MODULE assumptions ----
        |CONSTANT N
        |VARIABLE x
        |ASSUME(N = 4)
        |Init == x' = TRUE
        |Next == x' = ~x
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromSource("assumptions", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)

    modules(rootName).declarations(4) match {
      case TlaAssumeDecl(e) =>
        assert(OperEx(TlaOper.eq, NameEx("N"), ValEx(TlaInt(4))) == e)

      case e@_ =>
        fail("expected an assumption, found: " + e)
    }
  }

  test("ignore theorems") {
    // this proof is a garbage, just to check, whether the translator works
    val text =
      """
        |---- MODULE theorems ----
        |VARIABLE x
        |Init == x' = TRUE
        |Next == x' = ~x
        |Inv == x \in BOOLEAN
        |PTL == TRUE
        |THEOREM Next => Inv
        |<1>1. Init => Inv
        |  <2>1. Init => Inv
        |    BY DEF Init, Inv
        |  <2>. QED
        |    BY <2>1, PTL DEF Next
        |<1>2. QED
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = new SanyImporter(EnvironmentHandlerGenerator.makeEH, new SourceStore)
      .loadFromSource("theorems", Source.fromString(text))
    assert(1 == modules.size) // Naturals, Sequences, and our module
    // the root module and naturals
    val root = modules(rootName)
  }

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
