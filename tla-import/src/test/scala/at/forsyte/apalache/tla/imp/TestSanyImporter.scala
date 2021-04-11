package at.forsyte.apalache.tla.imp

import java.io.{File, PrintWriter}
import java.nio.file.Files
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.src.{SourcePosition, SourceRegion}
import at.forsyte.apalache.tla.lir.values._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx, _}
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalactic.source.Position
import org.scalatest.{BeforeAndAfter, FunSuite}
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.HashSet
import scala.io.Source

/**
 * Tests for the SANY importer.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestSanyImporter extends FunSuite with BeforeAndAfter {
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _

  before {
    sourceStore = new SourceStore
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
  }

  // assert that all declarations have source information
  def expectSourceInfoInDefs(module: TlaModule): Unit = {
    def assertForDecl(decl: TlaDecl): Unit = {
      assert(
          sourceStore.contains(decl.ID),
          s"(No source location for declaration $decl.name)"
      )
    }

    def collectDefs: TlaEx => Seq[TlaDecl] = {
      case LetInEx(body, defs @ _*) =>
        collectDefs(body) ++ defs.flatMap { d =>
          collectDefs(d.body)
        }

      case OperEx(_, args @ _*) =>
        args flatMap collectDefs

      case _ =>
        List()
    }

    for (decl <- module.declarations) {
      assertForDecl(decl)
      decl match {
        case operDecl: TlaOperDecl =>
          collectDefs(operDecl.body) foreach assertForDecl

        case _ => ()
      }
    }
  }

  def expectOperDecl(
      name: String, params: List[FormalParam], body: TlaEx
  ): (TlaDecl => Unit) = {
    case d: TlaOperDecl =>
      assert(name == d.name)
      assert(params == d.formalParams)
      assert(body == d.body)
      // the source location of the definition body has been saved
      assert(
          sourceStore.contains(d.body.ID),
          s"(Source location of the definition body ${d.body.ID} is not stored)"
      )
      // the source location of the definition has been saved
      assert(
          sourceStore.contains(d.ID),
          s"(Source of the definition ${d.name} is not stored)"
      )

    case d @ _ =>
      fail("Expected a TlaOperDecl, found: " + d)
  }

  def findAndExpectOperDecl(
      mod: TlaModule, name: String, params: List[FormalParam], body: TlaEx
  ): Unit = {
    mod.declarations.find {
      _.name == name
    } match {
      case Some(d: TlaOperDecl) =>
        expectOperDecl(name, params, body)

      case _ =>
        fail("Expected a TlaDecl")
    }
  }

  test("empty module") {
    val text =
      """---- MODULE justASimpleTest ----
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
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

    val (rootName, modules) = sanyImporter
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
      sanyImporter.loadFromSource("onevar", Source.fromString(text))
    val mod = expectSingleModule("onevar", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

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

    val (rootName, modules) = sanyImporter
      .loadFromSource("oneconst", Source.fromString(text))
    val mod = expectSingleModule("oneconst", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

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

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaInt(1)) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
        val loc = sourceStore.find(actionDecl.body.ID).get
        val expected = SourceRegion(SourcePosition(2, 9), SourcePosition(2, 9))
        assert(expected == loc.region)
    }
  }

  test("constant operator (decimal)") {
    val text =
      """---- MODULE constop ----
        |MyOp == 123.456
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaDecimal(BigDecimal("123.456"))) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
        val loc = sourceStore.find(actionDecl.body.ID).get
        val expected = SourceRegion(SourcePosition(2, 9), SourcePosition(2, 15))
        assert(expected == loc.region)
    }
  }

  test("constant operator (string)") {
    val text =
      """---- MODULE constop ----
        |MyOp == "Hello"
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaStr("Hello")) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
        val loc = sourceStore.find(actionDecl.body.ID).get
        val expected = SourceRegion(SourcePosition(2, 9), SourcePosition(2, 15))
        assert(expected == loc.region)
    }
  }

  test("constant operator (FALSE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == FALSE
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(false)) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
        val loc = sourceStore.find(actionDecl.body.ID).get
        assert("constop" == loc.filename)
        val expected = SourceRegion(SourcePosition(2, 9), SourcePosition(2, 13))
        assert(expected == loc.region)
    }
  }

  test("constant operator (TRUE)") {
    val text =
      """---- MODULE constop ----
        |MyOp == TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(true)) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(2 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(NameEx("x") == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
        val loc = sourceStore.find(actionDecl.body.ID).get
        val expected = SourceRegion(SourcePosition(4, 9), SourcePosition(4, 9))
        assert(expected == loc.region)
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("constop", Source.fromString(text))
    val mod = expectSingleModule("constop", rootName, modules)
    assert(2 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(NameEx("n") == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
    }
  }

  test("constant operator (a builtin operator)") {
    val text =
      """---- MODULE builtinop ----
        |MyOp == FALSE \/ TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("builtinop", Source.fromString(text))
    val mod = expectSingleModule("builtinop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(
            OperEx(TlaBoolOper.or, ValEx(TlaBool(false)), ValEx(TlaBool(true))) == actionDecl.body
        )
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
        val loc = sourceStore.find(actionDecl.body.ID).get
        val expected = SourceRegion(SourcePosition(2, 9), SourcePosition(2, 21))
        assert(expected == loc.region)
    }
  }

  test("LOCAL operator defined") {
    val text =
      """---- MODULE localop ----
        |LOCAL LocalOp == TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("localop", Source.fromString(text))
    val mod = expectSingleModule("localop", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    // when a local operator is defined in the main module, it is still accessible
    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("LocalOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(ValEx(TlaBool(true)) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
    }
  }

  test("LOCAL operator used") {
    val text =
      """---- MODULE localop ----
        |LOCAL LocalOp(X) == X
        |User(X) == LocalOp(X)
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("localop", Source.fromString(text))
    val mod = expectSingleModule("localop", rootName, modules)
    assert(2 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    // when a local operator is defined in the main module, it is still accessible
    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("LocalOp" == actionDecl.name)
        assert(1 == actionDecl.formalParams.length)
        assert(NameEx("X") == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
    }
  }

  test("LOCAL operator introducing name clashes") {
    val text =
      """---- MODULE localop ----
        |LOCAL Foo(X) ==
        |  LET A == X IN
        |  A
        | 
        |User(X) ==
        |  LET A == 1 IN  
        |  Foo(X)
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("localop", Source.fromString(text))
    val mod = expectSingleModule("localop", rootName, modules)
    assert(2 == mod.declarations.size)
    expectSourceInfoInDefs(mod)
    // no exceptions, all good
  }

  test("empty set") {
    val text =
      """---- MODULE emptyset ----
        |MyOp == {}
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("emptyset", Source.fromString(text))
    val mod = expectSingleModule("emptyset", rootName, modules)
    assert(1 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations.head match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        assert(OperEx(TlaSetOper.enumSet) == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
    }
  }

  test("constant operator (a builtin op and variables)") {
    val text =
      """---- MODULE builtinop ----
        |VARIABLE x
        |MyOp == x /\ TRUE
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("builtinop", Source.fromString(text))
    val mod = expectSingleModule("builtinop", rootName, modules)
    assert(2 == mod.declarations.size)
    expectSourceInfoInDefs(mod)

    mod.declarations(1) match {
      case actionDecl: TlaOperDecl =>
        assert("MyOp" == actionDecl.name)
        assert(0 == actionDecl.formalParams.length)
        val expected =
          OperEx(TlaBoolOper.and, NameEx("x"), ValEx(TlaBool(true)))
        assert(expected == actionDecl.body)
        assert(sourceStore.contains(actionDecl.body.ID)) // and source file information has been saved
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("builtins", Source.fromString(text))
    val mod = expectSingleModule("builtins", rootName, modules)
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectOperDecl(root, name, List(), body)

    val trueOperDecl = mod.declarations(1)
    expectDecl("True", ValEx(TlaBool(true)))

    val trueOperEx = OperEx(TlaOper.apply, NameEx("True"))

    expectDecl(
        "Eq",
        OperEx(TlaOper.eq, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    )
    expectDecl(
        "Ne",
        OperEx(TlaOper.ne, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    )
    expectDecl("Prime", OperEx(TlaActionOper.prime, NameEx("x")))
    expectDecl("Not", OperEx(TlaBoolOper.not, NameEx("x")))
    expectDecl(
        "Or",
        OperEx(TlaBoolOper.or, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    )
    expectDecl(
        "And",
        OperEx(TlaBoolOper.and, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    )
    expectDecl(
        "Equiv",
        OperEx(TlaBoolOper.equiv, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    )
    expectDecl(
        "Implies",
        OperEx(TlaBoolOper.implies, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    )
    expectDecl("Subset", OperEx(TlaSetOper.powerset, NameEx("x")))
    expectDecl("Union", OperEx(TlaSetOper.union, NameEx("x")))
    expectDecl("Domain", OperEx(TlaFunOper.domain, NameEx("x")))
    expectDecl(
        "Subseteq",
        OperEx(TlaSetOper.subseteq, NameEx("x"), NameEx("x"))
    )
    expectDecl("In", OperEx(TlaSetOper.in, NameEx("x"), NameEx("x")))
    expectDecl("Notin", OperEx(TlaSetOper.notin, NameEx("x"), NameEx("x")))
    expectDecl(
        "Setminus",
        OperEx(TlaSetOper.setminus, NameEx("x"), NameEx("x"))
    )
    expectDecl("Cap", OperEx(TlaSetOper.cap, NameEx("x"), NameEx("x")))
    expectDecl("Cup", OperEx(TlaSetOper.cup, NameEx("x"), NameEx("x")))
    expectDecl("Times", OperEx(TlaSetOper.times, NameEx("x"), NameEx("x")))
    expectDecl(
        "LeadsTo",
        OperEx(TlaTempOper.leadsTo, ValEx(TlaBool(true)), ValEx(TlaBool(true)))
    )
    expectDecl("Box", OperEx(TlaTempOper.box, ValEx(TlaBool(true))))
    expectDecl("Diamond", OperEx(TlaTempOper.diamond, ValEx(TlaBool(true))))
    expectDecl("Enabled", OperEx(TlaActionOper.enabled, NameEx("x")))
    expectDecl("Unchanged", OperEx(TlaActionOper.unchanged, NameEx("x")))
    expectDecl(
        "Cdot",
        OperEx(TlaActionOper.composition, trueOperEx, trueOperEx)
    )
    expectDecl(
        "Guarantees",
        OperEx(TlaTempOper.guarantees, trueOperEx, trueOperEx)
    )
    expectDecl(
        "Angleact",
        OperEx(TlaActionOper.nostutter, trueOperEx, NameEx("x"))
    )
    expectDecl(
        "BoundedChoose",
        OperEx(
            TlaOper.chooseBounded,
            NameEx("y"),
            NameEx("x"),
            ValEx(TlaBool(true))
        )
    )
    expectDecl(
        "BoundedExists",
        OperEx(TlaBoolOper.exists, NameEx("y"), NameEx("x"), ValEx(TlaBool(true)))
    )
    expectDecl(
        "BoundedForall",
        OperEx(TlaBoolOper.forall, NameEx("y"), NameEx("x"), ValEx(TlaBool(true)))
    )
    expectDecl(
        "CartesianProd",
        OperEx(TlaSetOper.times, NameEx("x"), NameEx("x"), NameEx("x"))
    )
    expectDecl(
        "Pair",
        OperEx(TlaFunOper.tuple, ValEx(TlaInt(1)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Tuple",
        OperEx(
            TlaFunOper.tuple,
            ValEx(TlaInt(1)),
            ValEx(TlaInt(2)),
            ValEx(TlaInt(3))
        )
    )
    expectDecl(
        "Case",
        OperEx(TlaControlOper.caseNoOther, 1.to(6).map(i => ValEx(TlaInt(i))): _*)
    )
    expectDecl(
        "CaseOther",
        OperEx(
            TlaControlOper.caseWithOther,
            (7 +: 1.to(6)).map(i => ValEx(TlaInt(i))): _*
        )
    )
    expectDecl(
        "ConjList",
        OperEx(
            TlaBoolOper.and,
            List(TlaBool(false), TlaBool(true), TlaBool(false))
              .map(b => ValEx(b)): _*
        )
    )
    expectDecl(
        "DisjList",
        OperEx(
            TlaBoolOper.or,
            List(TlaBool(false), TlaBool(true), TlaBool(false))
              .map(b => ValEx(b)): _*
        )
    )
    expectDecl(
        "Except",
        OperEx(
            TlaFunOper.except,
            NameEx("x"),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(0))),
            ValEx(TlaInt(1))
        )
    )
    expectDecl(
        "ExceptAt",
        OperEx(
            TlaFunOper.except,
            NameEx("x"),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(0))),
            OperEx(
                TlaBoolOper.and,
                OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(0))),
                ValEx(TlaBool(true))
            )
        )
    )
    expectDecl(
        "FcnApply",
        OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(1)))
    )
    val cup = OperEx(TlaSetOper.cup, NameEx("y"), NameEx("y"))
    expectDecl(
        "FcnCtor",
        OperEx(TlaFunOper.funDef, cup, NameEx("y"), NameEx("x"))
    )
    expectDecl(
        "FcnCtor2",
        OperEx(
            TlaFunOper.funDef,
            OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
            NameEx("a"),
            NameEx("x"),
            NameEx("b"),
            ValEx(TlaBoolSet)
        )
    )
    expectDecl(
        "FcnCtor3",
        OperEx(
            TlaFunOper.funDef,
            OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
            OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
            OperEx(TlaSetOper.times, NameEx("x"), ValEx(TlaBoolSet))
        )
    )
    expectDecl(
        "IfThenElse",
        OperEx(
            TlaControlOper.ifThenElse,
            ValEx(TlaBool(true)),
            ValEx(TlaBool(false)),
            ValEx(TlaBool(true))
        )
    )
    expectDecl(
        "RcdCtor",
        OperEx(
            TlaFunOper.enum,
            ValEx(TlaStr("a")),
            ValEx(TlaInt(1)),
            ValEx(TlaStr("b")),
            ValEx(TlaInt(2))
        )
    )
    expectDecl(
        "RcdSelect",
        OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaStr("foo")))
    )
    expectDecl(
        "SetEnumerate",
        OperEx(
            TlaSetOper.enumSet,
            ValEx(TlaInt(1)),
            ValEx(TlaInt(2)),
            ValEx(TlaInt(3))
        )
    )
    expectDecl("SetOfFcns", OperEx(TlaSetOper.funSet, NameEx("x"), NameEx("x")))
    expectDecl(
        "SetOfRcds",
        OperEx(
            TlaSetOper.recSet,
            ValEx(TlaStr("a")),
            NameEx("x"),
            ValEx(TlaStr("b")),
            NameEx("x")
        )
    )
    expectDecl(
        "StrongFairness",
        OperEx(TlaTempOper.strongFairness, NameEx("x"), trueOperEx)
    )
    expectDecl(
        "WeakFairness",
        OperEx(TlaTempOper.weakFairness, NameEx("x"), trueOperEx)
    )
    expectDecl(
        "SquareAct",
        OperEx(TlaActionOper.stutter, trueOperEx, NameEx("x"))
    )
    expectDecl(
        "TemporalExists",
        OperEx(TlaTempOper.EE, NameEx("y"), trueOperEx)
    )
    expectDecl(
        "TemporalForall",
        OperEx(TlaTempOper.AA, NameEx("y"), trueOperEx)
    )
    expectDecl(
        "UnboundedChoose",
        OperEx(TlaOper.chooseUnbounded, NameEx("y"), ValEx(TlaBool(true)))
    )
    expectDecl(
        "UnboundedExists",
        OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaBool(true)))
    )
    expectDecl(
        "UnboundedForall",
        OperEx(TlaBoolOper.forallUnbounded, NameEx("y"), ValEx(TlaBool(true)))
    )
    expectDecl(
        "SetOfAll",
        OperEx(TlaSetOper.map, ValEx(TlaInt(1)), NameEx("y"), NameEx("x"))
    )
    expectDecl(
        "SetOfTuples",
        OperEx(
            TlaSetOper.map,
            OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
            NameEx("a"),
            NameEx("x"),
            NameEx("b"),
            NameEx("x")
        )
    )
    expectDecl(
        "SubsetOf",
        OperEx(TlaSetOper.filter, NameEx("y"), NameEx("x"), ValEx(TlaBool(true)))
    )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("comprehensions", Source.fromString(text))
    val mod = expectSingleModule("comprehensions", rootName, modules)
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectOperDecl(root, name, List(), body)

    expectDecl(
        "FilterTuples",
        OperEx(
            TlaSetOper.filter,
            OperEx(TlaFunOper.tuple, NameEx("x"), NameEx("y")),
            NameEx("XY"),
            OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(1)))
        )
    ) ////
    expectDecl(
        "MapTuples",
        OperEx(
            TlaSetOper.map,
            OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(1))),
            OperEx(TlaFunOper.tuple, NameEx("x"), NameEx("y")),
            NameEx("XY")
        )
    ) ////
    expectDecl(
        "MapTuples2",
        OperEx(
            TlaSetOper.map,
            OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(1))),
            NameEx("x"),
            NameEx("XY"),
            NameEx("y"),
            NameEx("XY")
        )
    ) ////
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("composite", Source.fromString(text))
    val mod = expectSingleModule("composite", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(name: String, body: TlaEx): (TlaDecl => Unit) =
      expectOperDecl(name, List(), body)

    expectDecl(
        "Q1",
        OperEx(
            TlaBoolOper.exists,
            NameEx("x"),
            NameEx("X"),
            OperEx(
                TlaBoolOper.exists,
                NameEx("y"),
                NameEx("X"),
                ValEx(TlaBool(true))
            )
        )
    )(mod.declarations(2))
    expectDecl(
        "Q2",
        OperEx(
            TlaBoolOper.exists,
            NameEx("x"),
            NameEx("X"),
            OperEx(
                TlaBoolOper.exists,
                NameEx("y"),
                NameEx("X"),
                ValEx(TlaBool(true))
            )
        )
    )(mod.declarations(3))
    expectDecl(
        "Q3",
        OperEx(
            TlaBoolOper.exists,
            NameEx("x"),
            NameEx("X"),
            OperEx(
                TlaBoolOper.exists,
                NameEx("y"),
                NameEx("X"),
                OperEx(
                    TlaBoolOper.exists,
                    NameEx("z"),
                    NameEx("Z"),
                    ValEx(TlaBool(true))
                )
            )
        )
    )(mod.declarations(4))
    expectDecl(
        "Q4",
        OperEx(
            TlaBoolOper.exists,
            NameEx("x"),
            NameEx("X"),
            OperEx(
                TlaBoolOper.exists,
                NameEx("y"),
                NameEx("X"),
                OperEx(
                    TlaBoolOper.exists,
                    OperEx(TlaFunOper.tuple, NameEx("a"), NameEx("b")),
                    NameEx("Z"),
                    OperEx(
                        TlaBoolOper.exists,
                        NameEx("z"),
                        NameEx("Z"),
                        ValEx(TlaBool(true))
                    )
                )
            )
        )
    )(mod.declarations(5))
    expectDecl(
        "Q5",
        OperEx(
            TlaBoolOper.existsUnbounded,
            NameEx("x"),
            OperEx(TlaBoolOper.existsUnbounded, NameEx("y"), ValEx(TlaBool(true)))
        )
    )(mod.declarations(6))
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("except", Source.fromString(text))
    val mod = expectSingleModule("except", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(name: String, params: List[FormalParam], body: TlaEx) =
      expectOperDecl(name, params, body)

    expectDecl(
        "Except",
        List(),
        OperEx(
            TlaFunOper.except,
            NameEx("x"),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(0))),
            ValEx(TlaInt(1))
        )
    )(mod.declarations(1))

    expectDecl(
        "ExceptAt",
        List(),
        OperEx(
            TlaFunOper.except,
            NameEx("x"),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(0))),
            OperEx(
                TlaBoolOper.and,
                OperEx(TlaFunOper.app, NameEx("x"), ValEx(TlaInt(0))),
                ValEx(TlaBool(true))
            )
        )
    )(mod.declarations(2))

    expectDecl(
        "ExceptTuple",
        List(),
        OperEx(
            TlaFunOper.except,
            NameEx("x"),
            OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, ValEx(TlaInt(0)))),
            ValEx(TlaInt(1))
        )
    )(mod.declarations(3))

    // 1. The importer automatically substitutes @ with the corresponding function application
    // 2. The importer no longer unfolds ![1][2] to a chain of EXCEPTS. This is done by Desugarer in a separate pass.

    expectDecl(
        "ExceptManyAt",
        List(),
        OperEx(
            TlaFunOper.except,
            name("x"),
            tuple(int(1), int(2)),
            and(
                appFun(appFun(name("x"), int(1)), int(2)),
                bool(true)
            )
        )
    )(mod.declarations(4))

    /*  // the old test when Desugarer was part of SanyImporter
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
            ValEx(TlaBool(true)))
        )))(mod.declarations(4))
     */
  }

  test("expression labels") {
    val text =
      """---- MODULE labels ----
        |A == {FALSE} \cup (l1 :: {TRUE})
        |B == \E x \in BOOLEAN: l2(x) :: x /= FALSE
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("labels", Source.fromString(text))
    val mod = expectSingleModule("labels", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) =
      expectOperDecl(n, p, b)

    //    A == {FALSE} \cup (l1 :: {TRUE})
    val expectedABody =
      OperEx(
          TlaSetOper.cup,
          OperEx(TlaSetOper.enumSet, ValEx(TlaBool(false))),
          OperEx(
              TlaOper.label,
              OperEx(TlaSetOper.enumSet, ValEx(TlaBool(true))),
              ValEx(TlaStr("l1"))
          )
      ) ////
    expectDecl("A", List(), expectedABody)(mod.declarations.head)

    //    B == \E x \in BOOLEAN: l2(x) :: x /= FALSE
    // since we cannot access formal parameters, we ignore them
    val expectedBBody =
      OperEx(
          TlaBoolOper.exists,
          NameEx("x"),
          ValEx(TlaBoolSet),
          OperEx(
              TlaOper.label,
              OperEx(TlaOper.ne, NameEx("x"), ValEx(TlaBool(false))),
              ValEx(TlaStr("l2"))
          )
      ) ////
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("args", Source.fromString(text))
    val mod = expectSingleModule("args", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) =
      expectOperDecl(n, p, b)

    val expectedABody = OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaInt(2)))
    expectDecl("A", List(), expectedABody)(mod.declarations(4))

    val expectedBBody =
      OperEx(TlaFunOper.app, NameEx("g"), ValEx(TlaStr("green")))
    expectDecl("B", List(), expectedBBody)(mod.declarations(5))

    val expectedCBody =
      OperEx(TlaFunOper.app, NameEx("e"), ValEx(TlaBool(false)))
    expectDecl("C", List(), expectedCBody)(mod.declarations(6))

    val expectedDBody =
      OperEx(TlaFunOper.app, NameEx("h"), OperEx(TlaSetOper.enumSet))
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
        |E4 == [ f EXCEPT ![0] = [@ EXCEPT !.state = 4] ]
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("updates", Source.fromString(text))
    val mod = expectSingleModule("updates", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(name: String, body: TlaEx): (TlaDecl => Unit) =
      expectOperDecl(name, List(), body)

    expectDecl(
        "E1",
        OperEx(
            TlaFunOper.except,
            NameEx("f"),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(0))),
            ValEx(TlaInt(1)),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(2))),
            ValEx(TlaInt(3))
        )
    )(mod.declarations(1))

    // SanyImporter no longer unfolds a multi-argument EXCEPT into a chain.
    // This is done by Desugarer in a separate phase.
    expectDecl(
        "E2",
        except(
            name("f"),
            tuple(int(0), int(1), int(2)),
            int(3)
        )
    )(mod.declarations(2))

    expectDecl(
        "E3",
        OperEx(
            TlaFunOper.except,
            NameEx("f"),
            OperEx(TlaFunOper.tuple, OperEx(TlaFunOper.tuple, ValEx(TlaInt(0)), ValEx(TlaInt(1)), ValEx(TlaInt(2)))),
            ValEx(TlaInt(3))
        )
    )(mod.declarations(3))

    // using @ in EXCEPT: https://github.com/informalsystems/apalache/issues/286
    expectDecl(
        "E4",
        OperEx(
            TlaFunOper.except,
            NameEx("f"),
            OperEx(TlaFunOper.tuple, ValEx(TlaInt(0))),
            OperEx(
                TlaFunOper.except,
                OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaInt(0))), // this is the equivalent of @
                OperEx(TlaFunOper.tuple, ValEx(TlaStr("state"))),
                ValEx(TlaInt(4))
            )
        )
    )(mod.declarations(4))
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("selects", Source.fromString(text))
    val mod = expectSingleModule("selects", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(name: String, body: TlaEx): (TlaDecl => Unit) =
      expectOperDecl(name, List(), body)

    expectDecl(
        "S1",
        OperEx(
            TlaFunOper.app,
            OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaStr("a"))),
            ValEx(TlaStr("b"))
        )
    )(mod.declarations(1))
    expectDecl(
        "S2",
        OperEx(
            TlaFunOper.app,
            OperEx(
                TlaFunOper.app,
                OperEx(TlaFunOper.app, NameEx("f"), ValEx(TlaStr("a"))),
                ValEx(TlaStr("b"))
            ),
            ValEx(TlaStr("c"))
        )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("funCtor", Source.fromString(text))
    val mod = expectSingleModule("funCtor", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(name: String, body: TlaEx) =
      expectOperDecl(name, List(), body)

    expectDecl(
        "C1",
        OperEx(
            TlaFunOper.funDef,
            ValEx(TlaBool(true)),
            NameEx("x"),
            NameEx("X"),
            NameEx("y"),
            NameEx("X")
        )
    )(mod.declarations(2))
    expectDecl(
        "C2",
        OperEx(
            TlaFunOper.funDef,
            ValEx(TlaBool(true)),
            NameEx("x"),
            NameEx("X"),
            NameEx("y"),
            NameEx("X")
        )
    )(mod.declarations(3))
    expectDecl(
        "C3",
        OperEx(
            TlaFunOper.funDef,
            ValEx(TlaBool(true)),
            NameEx("x"),
            NameEx("X"),
            NameEx("y"),
            NameEx("X"),
            NameEx("z"),
            NameEx("Z")
        )
    )(mod.declarations(4))

    // the tuple <<a, b>> is no longer collapsed to a_b by SanyImporter.
    // This is done by Desugarer in a separate phase.
    expectDecl(
        "C4",
        funDef(
            bool(true),
            name("x"),
            name("X"),
            name("y"),
            name("X"),
            tuple(name("a"), name("b")),
            name("Z"),
            name("z"),
            name("Z")
        )
    )(mod.declarations(5))

    // the old test when Desugarer was part of SanyImporter
    /*
    expectDecl("C4",
      OperEx(TlaFunOper.funDef,
        ValEx(TlaBool(true)),
        NameEx("x"), NameEx("X"),
        NameEx("y"), NameEx("X"),
        NameEx("a_b"), NameEx("Z"), // the tuple <<a, b>> is collapsed to a_b by Desugarer
        NameEx("z"), NameEx("Z")
      ))(mod.declarations(5))
     */
  }

  test("weird set comprehension") {
    val text =
      """---- MODULE weird ----
        |VARIABLE S
        |Op == { x \in S: x \in S }
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("weird", Source.fromString(text))
    val mod = expectSingleModule("weird", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(name: String, body: TlaEx) =
      expectOperDecl(name, List(), body)

    val filter =
      OperEx(
          TlaSetOper.filter,
          NameEx("x"),
          NameEx("S"),
          OperEx(TlaSetOper.in, NameEx("x"), NameEx("S"))
      )
    expectDecl("Op", filter)(mod.declarations(1))
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("level1Operators", Source.fromString(text))
    val mod = expectSingleModule("level1Operators", rootName, modules)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) =
      expectOperDecl(n, p, b)

    expectDecl(
        "A",
        List(SimpleFormalParam("i"), SimpleFormalParam("j")),
        OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j"))
    )(mod.declarations(2))
    expectDecl(
        "**",
        List(SimpleFormalParam("i"), SimpleFormalParam("j")),
        OperEx(TlaSetOper.cap, NameEx("i"), NameEx("j"))
    )(mod.declarations(3))
    val aDecl = mod.declarations(2).asInstanceOf[TlaOperDecl]
    expectDecl(
        "C",
        List(),
        OperEx(
            TlaOper.apply,
            NameEx(aDecl.name),
            ValEx(TlaInt(1)),
            ValEx(TlaInt(2))
        )
    )(mod.declarations(4))
  }

  test("level-2 operators") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE level2Operators ----
        |VARIABLE x, y
        |A(i, j, f(_)) == f(i \cup j)
        |B(z) == {z}
        |C == A(0, 1, B)
        |\* regression for bug #575
        |D(f(_)) ==
        |  LET E(g(_)) == g(3) IN
        |  E(f)
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("level2Operators", Source.fromString(text))
    val mod = expectSingleModule("level2Operators", rootName, modules)
    expectSourceInfoInDefs(mod)

    def expectDecl(n: String, p: List[FormalParam], b: TlaEx) =
      expectOperDecl(n, p, b)

    expectDecl(
        "A",
        List(
            SimpleFormalParam("i"),
            SimpleFormalParam("j"),
            OperFormalParam("f", 1)
        ),
        OperEx(
            TlaOper.apply,
            NameEx("f"),
            OperEx(TlaSetOper.cup, NameEx("i"), NameEx("j"))
        )
    )(mod.declarations(2))
    val aDecl = mod.declarations(2).asInstanceOf[TlaOperDecl]
    expectDecl("C", List(), appDecl(aDecl, int(0), int(1), name("B")))(
        mod.declarations(4)
    )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("let", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations
      .find {
        _.name == "A"
      }
      .collect { case TlaOperDecl(_, _, LetInEx(body, defs @ _*)) =>
        assert(sourceStore.contains(body.ID))
        assert(3 == defs.length)
        val xDecl = defs.head
        assert("X" == xDecl.name)
        val yDecl = defs(1)
        assert(
            TlaOperDecl("Y", List(SimpleFormalParam("a")), NameEx("a")) == yDecl
        )
        assert(sourceStore.contains(yDecl.body.ID)) // and source file information has been saved

        val zDecl = defs(2)
        zDecl match {
          case TlaOperDecl(
                  "Z",
                  List(OperFormalParam("f", 1), SimpleFormalParam("a")),
                  _
              ) =>
            assert(
                OperEx(TlaOper.apply, NameEx("f"), NameEx("a")) == zDecl.body
            )
        }
        assert(sourceStore.contains(zDecl.body.ID)) // and source file information has been saved
        assert(0 == xDecl.formalParams.length)
        assert(int(1).untyped() == xDecl.body)
        // although "X" might seem to be a variable, it is actually an operator without any arguments
        assert(appDecl(xDecl).untyped() == body)
        assert(sourceStore.contains(xDecl.body.ID)) // and source file information has been saved
      }
  }

  test("LAMBDA") {
    val text =
      """---- MODULE lambda ----
        |A(F(_), x) == F(x)
        |B(y) ==
        |  A(LAMBDA x: x = 1, 2)
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("lambda", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    root.declarations.find {
      _.name == "B"
    } collect {
      case TlaOperDecl(
              _,
              _,
              OperEx(TlaOper.apply, NameEx("A"), lambda, ValEx(TlaInt(i)))
          ) =>
        lambda match {
          case LetInEx(
                  NameEx("LAMBDA"),
                  TlaOperDecl(
                      "LAMBDA",
                      List(SimpleFormalParam("x")),
                      OperEx(TlaOper.eq, NameEx("x"), ValEx(TlaInt(_)))
                  )
              ) =>
          // ok

          case _ =>
            fail("expected a LET-IN definition of LAMBDA and its usage by name")
        }

      case _ => fail("expected A")
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("let", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find {
      _.name == "A"
    } collect { case TlaOperDecl(_, _, LetInEx(body, defs @ _*)) =>
      assert(2 == defs.length)
      val fDecl = defs.head
      assert("f" == fDecl.name)
      val expectedBody =
        OperEx(
            TlaFunOper.recFunDef,
            OperEx(TlaFunOper.app, OperEx(TlaFunOper.recFunRef), NameEx("x")),
            NameEx("x"),
            ValEx(TlaBoolSet)
        )

      assert(expectedBody == fDecl.body)
      assert(sourceStore.contains(fDecl.body.ID)) // and source file information has been saved

      val xDecl = defs(1)
      assert("X" == xDecl.name)
      assert(appOp(name("X")).untyped() == xDecl.body)
      assert(appDecl(xDecl).untyped() == body)
      assert(sourceStore.contains(xDecl.body.ID)) // and source file information has been saved
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("recOpers", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def assertRec(name: String, nparams: Int, expectedBody: TlaEx) = {
      root.declarations.find {
        _.name == name
      } match {
        case Some(d: TlaOperDecl) =>
          // We expect that R in the declaration body is referred by a formal parameter with the same name R.
          // The caveat here is that the formal parameter R does not appear in the list of the R's formal parameters,
          // but it is accessible via the field recParam.
          assert(d.isRecursive)
          val recParam = OperFormalParam(name, nparams)
          assert(d.body == expectedBody)
          assert(sourceStore.contains(d.body.ID)) // and source file information has been saved

        case _ =>
          fail("expected TlaRecOperDecl")
      }
    }

    // in the recursive sections, the calls to recursive operators should be replaced with (apply ...)
    assertRec("R", 1, OperEx(TlaOper.apply, NameEx("R"), NameEx("n")))

    assertRec("A", 1, OperEx(TlaOper.apply, NameEx("B"), NameEx("n")))
    assertRec("B", 1, OperEx(TlaOper.apply, NameEx("C"), NameEx("n")))
    assertRec("C", 1, OperEx(TlaOper.apply, NameEx("A"), NameEx("n")))

    assertRec("X", 0, OperEx(TlaOper.apply, NameEx("X")))

    // however, in non-recursive sections, the calls to recursive operators are just normal OperEx(operator, ...)
    root.declarations.find {
      _.name == "D"
    } match {
      case Some(d: TlaOperDecl) =>
        val A = root.declarations
          .find {
            _.name == "A"
          }
          .get
          .asInstanceOf[TlaOperDecl]
        assert(appDecl(A, name("n")).untyped() == d.body)
        assert(sourceStore.contains(d.body.ID)) // and source file information has been saved

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
        val recParam = OperFormalParam("F", 1)
        val ite = OperEx(
            TlaControlOper.ifThenElse,
            OperEx(TlaOper.eq, NameEx("n"), ValEx(TlaInt(0))),
            ValEx(TlaInt(1)),
            OperEx(
                TlaArithOper.mult,
                NameEx("n"),
                OperEx(
                    TlaOper.apply,
                    NameEx("F"),
                    OperEx(TlaArithOper.minus, NameEx("n"), ValEx(TlaInt(1)))
                )
            )
        )
        assert(d.body == ite)
        assert(sourceStore.contains(d.body.ID)) // and source file information has been saved

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
        |recFun2[x \in S, y \in S] == recFun2[y, x]
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("globalFuns", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def assertTlaRecFunDecl(expectedName: String, body: TlaEx): Unit = {
      root.declarations.find {
        _.name == expectedName
      } match {
        case Some(d: TlaOperDecl) =>
          assert(expectedName == d.name)
          assert(body == d.body)
          assert(!d.isRecursive)
          assert(sourceStore.contains(d.body.ID)) // and source file information has been saved

        case _ =>
          fail("Expected a TlaOperDecl")
      }
    }

    assertTlaRecFunDecl(
        "nonRecFun",
        OperEx(TlaFunOper.funDef, NameEx("x"), NameEx("x"), NameEx("S"))
    )

    assertTlaRecFunDecl(
        "recFun",
        OperEx(
            TlaFunOper.recFunDef,
            OperEx(TlaFunOper.app, OperEx(TlaFunOper.recFunRef), NameEx("x")),
            NameEx("x"),
            NameEx("S")
        )
    )

    val bodyOfFun2 = OperEx(
        TlaFunOper.app,
        OperEx(TlaFunOper.recFunRef),
        OperEx(TlaFunOper.tuple, NameEx("y"), NameEx("x"))
    )
    assertTlaRecFunDecl(
        "recFun2",
        OperEx(
            TlaFunOper.recFunDef,
            bodyOfFun2,
            NameEx("x"),
            NameEx("S"),
            NameEx("y"),
            NameEx("S")
        )
    )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("inst", Source.fromString(text))
    assert(2 == modules.size) // inst + Naturals
    // the root module and A
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectOperDecl(root, name, List(), body)

    // the root module contains its own declarations and the declarations by FiniteSets
    root.declarations.find { _.name == "J!F" } match {
      case Some(
              TlaOperDecl(
                  _,
                  params,
                  OperEx(TlaArithOper.plus, NameEx("x"), NameEx("M"))
              )
          ) =>
        assert(params.length == 1)
        assert(params.head.isInstanceOf[SimpleFormalParam])
        assert("x" == params.head.asInstanceOf[SimpleFormalParam].name)

      case e =>
        fail("expected the body for J!F, found: " + e)
    }
    val fDecl = root.declarations.find { _.name == "J!F" }.get
    root.declarations.find { _.name == "J!G" } match {
      case Some(TlaOperDecl(_, params, body)) =>
        assert(params.isEmpty)
        val expected: TlaEx = appDecl(fDecl.asInstanceOf[TlaOperDecl], int(3))
        assert(body == expected)

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

  test("EXTENDS of the standard modules") {
    // operators with parameters that are themselves operators with parameters
    val text =
      """---- MODULE imports ----
        |EXTENDS Naturals
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("imports", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(root.declarations.isEmpty)
    // as Naturals containts definitions of the built-in operators, it is empty
    val naturals = modules("Naturals")
    assert(naturals.declarations.isEmpty)
  }

  test("lookup order in INSTANCE") {
    // regression: SanyImporter was resolving the names in the wrong order
    val text =
      """---- MODULE imports ----
        |---- MODULE M ----
        |a == {}
        |b == a
        |================================
        |a(self) == {self}
        |I == INSTANCE M
        |c == a(1)
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("imports", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(4 == root.declarations.size)
    val aOfM = root.declarations.head
    // check that the root module has indeed the definition a(self) == {self}, not a == {}
    assert(
        aOfM.isInstanceOf[TlaOperDecl] && aOfM
          .asInstanceOf[TlaOperDecl]
          .formalParams
          .size == 1
    )
  }

  test("substitution in INSTANCE") {
    // regression: the importer was not able to substitute a variable with an operator, e.g., in Paxos
    val text =
      """---- MODULE Paxos ----
        |---- MODULE Consensus ----
        |VARIABLE chosen
        |C == chosen
        |================================
        |---- MODULE Voting ----
        |chosen == 1
        |C == INSTANCE Consensus
        |================================
        |V == INSTANCE Voting
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("Paxos", Source.fromString(text))
    assert(1 == modules.size)
    expectSourceInfoInDefs(modules(rootName))
  }

  test("LOCAL operator inside INSTANCE") {
    val text =
      """---- MODULE localInInstance ----
        |---- MODULE M ----
        |LOCAL a == {}
        |b == a
        |================================
        |I == INSTANCE M
        |c == I!b
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("localInInstance", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(2 == root.declarations.size)
    val bOfM = root.declarations.head
    // as "a" is LOCAL, it does not appear in the declarations, but it becomes a LET-IN definition inside b
    assert("I!b" == bOfM.name)
    // BUGFIX #576: use a unique lookup prefix to guarantee name uniqueness
    bOfM match {
      case TlaOperDecl(name, List(), LetInEx(OperEx(TlaOper.apply, NameEx(appliedName)), localDef)) =>
        assert("I!b" == name)
        assert(appliedName.startsWith("LOCAL"))
        assert(appliedName.endsWith("!I!a"))
        localDef match {
          case TlaOperDecl(localName, List(), body) =>
            assert(appliedName == localName)
            assert(OperEx(TlaSetOper.enumSet) == body)

          case _ =>
            fail("Expected an operator definition " + appliedName)
        }

      case _ => fail("Unexpected operator structure")
    }
  }

  // regression for #112
  test("LET-IN inside INSTANCE") {
    val text =
      """---- MODULE letInInstance ----
        |---- MODULE M ----
        |VARIABLE x
        |a ==
        |  LET b == {} IN
        |  b
        |================================
        |VARIABLE x
        |INSTANCE M
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("letInInstance", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(2 == root.declarations.size)
    val aOfM = root.declarations(1)
    aOfM.asInstanceOf[TlaOperDecl].body match {
      case LetInEx(body, bDecl) =>
        assert(sourceStore.contains(body.ID))
        assert(sourceStore.contains(bDecl.body.ID))

      case _ =>
        fail("expected declaration of b")
    }
  }

  // regression for #143
  test("Lookup inside substitutions") {
    val text =
      """------------------- MODULE P ----------------------
        |------------------- MODULE Vot ----------------------
        |------------------- MODULE Cons -------------------
        |VARIABLE chosen
        |Init == chosen = {}
        |Next == chosen = {2}
        |===================================================
        |chosen == {2}
        |C == INSTANCE Cons
        |===================================================
        |V == INSTANCE Vot
        |===================================================""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("P", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // expect V!chosen, V!C!Init and V!C!Next
    assert(3 == root.declarations.size)
    val next = root.declarations
      .find(_.name == "V!C!Next")
      .getOrElse(fail("V!C!Next not found"))
    assert("V!C!Next" == next.name)
    next.asInstanceOf[TlaOperDecl].body match {
      case body @ OperEx(
              TlaOper.eq,
              OperEx(TlaOper.apply, NameEx("V!chosen")),
              OperEx(TlaSetOper.enumSet, ValEx(TlaInt(i)))
          ) =>
        assert(i == 2)
        assert(sourceStore.contains(body.ID))

      case _ =>
        fail("expected V!C!Next == V!chosen = {2}")
    }
  }

  // regression for #143
  test("Series of substitutions") {
    val text =
      """------------------- MODULE A ----------------------
        |------------------- MODULE B ----------------------
        |------------------- MODULE C -------------------
        |VARIABLE x
        |magic == x /= 2
        |===================================================
        |VARIABLE y
        |C1 == INSTANCE C WITH x <- y
        |===================================================
        |VARIABLE z
        |B1 == INSTANCE B WITH y <- z
        |===================================================""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("A", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // expect B1!C1!magic and z
    assert(2 == root.declarations.size)
    val magic = root.declarations
      .find(_.name == "B1!C1!magic")
      .getOrElse(fail("B1!C1!magic not found"))
    assert("B1!C1!magic" == magic.name)
    magic.asInstanceOf[TlaOperDecl].body match {
      case body @ OperEx(TlaOper.ne, NameEx("z"), ValEx(TlaInt(i))) =>
        assert(i == 2)
        assert(sourceStore.contains(body.ID))

      case _ =>
        fail("expected B1!C1!magic == z /= 2")
    }
  }

  // This test works due a temporary bugfix for issue #130.
  // We should test it again, once the bug in SANY is fixed.
  test("RECURSIVE operator inside INSTANCE") {
    val text =
      """---- MODULE recInInstance ----
        |---- MODULE M ----
        |RECURSIVE a(_)
        |a(X) == a(X)
        |================================
        |RECURSIVE b(_)
        |b(X) == b(X)
        |I == INSTANCE M
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("recInInstance", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // we strip away the operator declarations by Naturals
    assert(2 == root.declarations.size)
    val b = root.declarations.head
    assert("b" == b.name)
    assert(b.asInstanceOf[TlaOperDecl].isRecursive)
    val aOfM = root.declarations(1)
    // I!a should be recursive
    assert("I!a" == aOfM.name)
    assert(aOfM.asInstanceOf[TlaOperDecl].isRecursive)
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
        |Leq2 == 3 =< 2
        |Geq == 3 >= 2
        |Mod == 3 % 2
        |Div == 3 \div 2
        |Range == 2 .. 3
        |
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("nats", Source.fromString(text))
    assert(2 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx): Unit =
      findAndExpectOperDecl(root, name, List(), body)

    // the root module contains its own declarations and the declarations by Naturals
    expectDecl("NatSet", ValEx(TlaNatSet))
    expectDecl(
        "Plus",
        OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Minus",
        OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Mult",
        OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Power",
        OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Less",
        OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Greater",
        OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Leq",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Leq2",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Geq",
        OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Mod",
        OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Div",
        OperEx(TlaArithOper.div, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Range",
        OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3)))
    )

    // check the source info
    val plus = root.declarations.find {
      _.name == "Plus"
    } match {
      case Some(TlaOperDecl(_, _, oe @ OperEx(oper, _*))) =>
        val loc = sourceStore.find(oe.ID).get
        assert(
            SourceRegion(SourcePosition(4, 9), SourcePosition(4, 13)) == loc.region
        )

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

    val (rootName, modules) = sanyImporter
      .loadFromSource("ints", Source.fromString(text))
    assert(3 == modules.size) // Integers extends Naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(13 == root.declarations.size)

    // the root module contains its own declarations and the declarations by Integers
    expectDecl("IntSet", ValEx(TlaIntSet))
    expectDecl(
        "Plus",
        OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Minus",
        OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Mult",
        OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Power",
        OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Less",
        OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Greater",
        OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Leq",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Geq",
        OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Mod",
        OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Div",
        OperEx(TlaArithOper.div, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Range",
        OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3)))
    )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("reals", Source.fromString(text))
    assert(4 == modules.size) // Reals include Integers that include Naturals
    val root = modules(rootName)
    // the definitions of the standard operators are filtered out
    assert(15 == root.declarations.size)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    expectDecl("RealSet", ValEx(TlaRealSet))
    expectDecl("Inf", ValEx(TlaRealInfinity))
    expectDecl(
        "Plus",
        OperEx(TlaArithOper.plus, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Minus",
        OperEx(TlaArithOper.minus, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Mult",
        OperEx(TlaArithOper.mult, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Power",
        OperEx(TlaArithOper.exp, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Less",
        OperEx(TlaArithOper.lt, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Greater",
        OperEx(TlaArithOper.gt, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Leq",
        OperEx(TlaArithOper.le, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Geq",
        OperEx(TlaArithOper.ge, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Mod",
        OperEx(TlaArithOper.mod, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Div",
        OperEx(TlaArithOper.div, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
    expectDecl(
        "Range",
        OperEx(TlaArithOper.dotdot, ValEx(TlaInt(2)), ValEx(TlaInt(3)))
    )
    expectDecl("UnaryMinus", OperEx(TlaArithOper.uminus, ValEx(TlaInt(2))))
    expectDecl(
        "RealDiv",
        OperEx(TlaArithOper.realDiv, ValEx(TlaInt(3)), ValEx(TlaInt(2)))
    )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("sequences", Source.fromString(text))
    assert(3 == modules.size) // Naturals, Sequences, and our module
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(11 == root.declarations.size)

    expectDecl("Empty", tuple())
    expectDecl("Three", tuple(int(1), int(2), int(3)))
    expectDecl("ASeq", seqSet(enumSet(int(1), int(2))))
    expectDecl("ALen", len(tuple(int(1), int(2), int(3))))
    expectDecl("AConcat", concat(tuple(int(1), int(2)), tuple(int(3))))
    expectDecl("AAppend", append(tuple(int(1), int(2)), int(3)))
    expectDecl("AHead", head(tuple(int(1), int(2), int(3))))
    expectDecl("ATail", tail(tuple(int(1), int(2), int(3))))
    expectDecl(
        "ASubSeq",
        subseq(tuple(int(1), int(2), int(3), int(4)), int(2), int(3))
    )
    expectDecl(
        "ASelectSeq",
        selectseq(tuple(int(1), int(2), int(3), int(4)), name("Test"))
    )
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("finitesets", Source.fromString(text))
    assert(4 == modules.size) // Naturals, Sequences, FiniteSets, and our module
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(2 == root.declarations.size)

    // the root module contains its own declarations and the declarations by FiniteSets
    expectDecl(
        "IsFinSet",
        OperEx(TlaFiniteSetOper.isFiniteSet, ValEx(TlaBoolSet))
    )
    expectDecl("Card", OperEx(TlaFiniteSetOper.cardinality, ValEx(TlaBoolSet)))
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("tlc", Source.fromString(text))
    assert(5 == modules.size) // our module + 4 LOCAL modules
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    def expectDecl(name: String, body: TlaEx) =
      findAndExpectOperDecl(root, name, List(), body)

    // the definitions of the standard operators are filtered out
    assert(16 == root.declarations.size)

    expectDecl("APrint", OperEx(TlcOper.print, str("TLC Print"), bool(true)))
    expectDecl("APrintT", OperEx(TlcOper.printT, str("TLC PrintT")))
    expectDecl("AAssert", OperEx(TlcOper.assert, str("TLC Assert"), bool(true)))
    expectDecl("AJavaTime", OperEx(TlcOper.javaTime))
    expectDecl("ATLCGet", OperEx(TlcOper.tlcGet, name("i")))
    expectDecl("ATLCSet", OperEx(TlcOper.tlcSet, name("i"), int(3)))
    expectDecl(
        "AColonGreater",
        OperEx(TlcOper.colonGreater, enumSet(int(1), int(2)), int(3))
    )
    val fun12 = funDef(name("j"), name("j"), enumSet(int(1), int(2)))
    val fun34 = funDef(name("k"), name("k"), enumSet(int(3), int(4)))
    expectDecl("AtAt", OperEx(TlcOper.atat, fun12, fun34))
    expectDecl(
        "APermutations",
        OperEx(TlcOper.permutations, tuple(int(1), int(2)))
    )
    expectDecl(
        "ASortSeq",
        OperEx(TlcOper.sortSeq, tuple(int(2), int(1)), name("FakeSort"))
    )
    expectDecl(
        "ARandomElement",
        OperEx(TlcOper.randomElement, enumSet(int(1), int(2)))
    )
    expectDecl("AAny", OperEx(TlcOper.any))
    expectDecl("ATLCEval", OperEx(TlcOper.tlcEval, int(42)))
    expectDecl("AToString", OperEx(TlcOper.tlcToString, int(42)))
  }

  test("EXTENDS Bags") {
    // currently, Bags is imported as a user-defined module, no built-in operators are introduced
    val text =
      """---- MODULE localSum ----
        |EXTENDS Bags
        |================================
      """.stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("localSum", Source.fromString(text))
    assert(6 == modules.size) // Naturals, Sequences, TLC, FiniteSets, Bags, and our module

    val root = modules("localSum")
    expectSourceInfoInDefs(root)
    // this number may change when a new version of Bags.tla is shipped in tla2tools.jar
    assert(13 == root.declarations.size)
  }

  test("EXTENDS Apalache") {
    val text =
      """---- MODULE root ----
        |EXTENDS Integers, FiniteSets, Apalache
        |VARIABLE x, S
        |
        |Assn == x' := 1
        |Sklm == Skolem(\E y \in S: TRUE)
        |Expnd == Expand(SUBSET S)
        |CC == ConstCardinality(Cardinality(S) >= 2)
        |================================
      """.stripMargin

    // We have to set TLA-Library, in order to look up Apalache.tla. This is done automatically in pom.xml.
    // If you run this test in an IDE, and the test fails, add the following line to the VM parameters
    // (don't forget to replace <APALACHE_HOME> with the directory where you checked out the project):
    //
    // -DTLA-Library=<APALACHE_HOME>/src/tla
    System.out.println(
        "TLA-Library = %s".format(System.getProperty("TLA-Library"))
    )

    val (rootName, modules) = sanyImporter
      .loadFromSource("root", Source.fromString(text))
    assert(6 == modules.size) // root, Apalache, Integers, FiniteSets, and whatever they import

    val root = modules("root")
    expectSourceInfoInDefs(root)
    assert(6 == root.declarations.size)

    def expectDecl(name: String, body: TlaEx) = {
      findAndExpectOperDecl(root, name, List(), body)
    }

    expectDecl(
        "Assn",
        OperEx(
            ApalacheOper.assign,
            OperEx(TlaActionOper.prime, NameEx("x")),
            ValEx(TlaInt(1))
        )
    )
    expectDecl(
        "Sklm",
        OperEx(
            ApalacheOper.skolem,
            OperEx(
                TlaBoolOper.exists,
                NameEx("y"),
                NameEx("S"),
                ValEx(TlaBool(true))
            )
        )
    )
    expectDecl(
        "Expnd",
        OperEx(ApalacheOper.expand, OperEx(TlaSetOper.powerset, NameEx("S")))
    )
    expectDecl(
        "CC",
        OperEx(
            ApalacheOper.constCard,
            OperEx(
                TlaArithOper.ge,
                OperEx(TlaFiniteSetOper.cardinality, NameEx("S")),
                ValEx(TlaInt(2))
            )
        )
    )
  }

  test("assumptions") {
    // checking that the assumptions are imported properly
    val text =
      """
        |---- MODULE assumptions ----
        |CONSTANT N
        |ASSUME N = 4
        |ASSUME N /= 10
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("assumptions", Source.fromString(text))
    assert(1 == modules.size)
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)

    modules(rootName).declarations(1) match {
      case TlaAssumeDecl(e) => assert(eql(name("N"), int(4)).untyped() == e)

      case e @ _ => fail("expected an assumption, found: " + e)
    }

    modules(rootName).declarations(2) match {
      case TlaAssumeDecl(e) => assert(neql(name("N"), int(10)).untyped() == e)

      case e @ _ => fail("expected an assumption, found: " + e)
    }

    // regression test for issue #25
    val names = HashSet(modules(rootName).assumeDeclarations.map(_.name): _*)
    assert(2 == names.size) // all assumptions must have unique names
  }

  test("instances of standard modules") {
    // Issue #52: the built-in operators are not eliminated when using INSTANCE
    val text =
      """---- MODULE issue52 ----
        |I == INSTANCE Sequences
        |A == I!Append(<<>>, {})
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("issue52", Source.fromString(text))
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // the definitions of the standard operators are filtered out
    assert(1 == root.declarations.size)
    root.declarations(0) match {
      case TlaOperDecl("A", _, body) =>
        assert(append(tuple(), enumSet()).untyped() == body)

      case d => fail("unexpected declaration: " + d)
    }
  }

  test("operators of local instances of the standard modules") {
    // Issue #295: the built-in operators are not eliminated when using LOCAL INSTANCE
    val text =
      """---- MODULE issue295 ----
        |---- MODULE A ----
        |LOCAL INSTANCE Sequences
        |A == Append(<<>>, {})
        |==================
        |INSTANCE A
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("issue295", Source.fromString(text))
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // the definitions of the standard operators are filtered out
    assert(1 == root.declarations.size)
    root.declarations(0) match {
      case TlaOperDecl("A", _, body) =>
        assert(append(tuple(), enumSet()).untyped() == body)

      case d => fail("unexpected declaration: " + d)
    }
  }

  test("values of local instances of the standard modules") {
    // Issue #295: the built-in operators are not eliminated when using LOCAL INSTANCE
    val text =
      """---- MODULE issue295 ----
        |---- MODULE A ----
        |LOCAL INSTANCE Integers
        |A == Int
        |==================
        |INSTANCE A
        |================================
        |""".stripMargin

    val (rootName, modules) = sanyImporter
      .loadFromSource("issue295", Source.fromString(text))
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
    // the definitions of the standard operators are filtered out
    assert(1 == root.declarations.size)
    root.declarations(0) match {
      case TlaOperDecl("A", _, body) =>
        assert(ValEx(TlaIntSet) == body)

      case d => fail("unexpected declaration: " + d)
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

    val (rootName, modules) = sanyImporter
      .loadFromSource("theorems", Source.fromString(text))
    assert(1 == modules.size) // Naturals, Sequences, and our module
    // the root module and naturals
    val root = modules(rootName)
    expectSourceInfoInDefs(root)
  }

  ////////////////////////////////////////////////////////////////////
  private def expectSingleModule(
      expectedRootName: String, rootName: String, modules: Map[String, TlaModule]
  ): TlaModule = {
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
