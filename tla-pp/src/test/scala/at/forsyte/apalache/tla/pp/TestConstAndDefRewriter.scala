package at.forsyte.apalache.tla.pp

import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.SanyImporter
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.{IntT1, OperT1, SimpleFormalParam, TlaModule, TlaOperDecl, Typed}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import scala.io.Source

@RunWith(classOf[JUnitRunner])
class TestConstAndDefRewriter extends FunSuite with BeforeAndAfterEach {
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _

  override def beforeEach() {
    sourceStore = new SourceStore()
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
  }

  test("override a constant") {
    val text =
      """---- MODULE const ----
        |CONSTANT n
        |OVERRIDE_n == 10
        |A == {n}
        |================================
      """.stripMargin

    val (rootName, modules) =
      sanyImporter.loadFromSource("const", Source.fromString(text))
    val root = modules(rootName)
    // we don't want to run a type checker, so we just hack the type of the declaration n
    val newDeclarations =
      root.declarations match {
        case Seq(n, overrideN: TlaOperDecl, rest @ _*) =>
          val typedN = n.withTag(Typed(IntT1()))
          val overrideTag = Typed(OperT1(Seq(), IntT1()))
          val typedOverrideN = TlaOperDecl(overrideN.name, List(), overrideN.body.withTag(Typed(IntT1())))(overrideTag)
          Seq(typedN, typedOverrideN) ++ rest
      }

    val input = new TlaModule(root.name, newDeclarations)

    val rewritten = new ConstAndDefRewriter(new IdleTracker())(input)
    assert(rewritten.constDeclarations.isEmpty) // no constants anymore
    assert(rewritten.operDeclarations.size == 2)
    val expected_n = TlaOperDecl("n", List(), tla.int(10))
    assert(expected_n == rewritten.operDeclarations.head)
    val expected_A = TlaOperDecl("A", List(), tla.enumSet(tla.appOp(tla.name("n"))))
    assert(expected_A == rewritten.operDeclarations(1))
  }

  // In TLA+, constants may be operators with multiple arguments.
  // We do not support that yet.
  test("override a constant with a unary operator") {
    val text =
      """---- MODULE const ----
        |CONSTANT n
        |OVERRIDE_n(x) == x
        |A == {n}
        |================================
      """.stripMargin

    val (rootName, modules) =
      sanyImporter.loadFromSource("const", Source.fromString(text))
    val root = modules(rootName)
    assertThrows[OverridingError](new ConstAndDefRewriter(new IdleTracker())(root))
  }

  test("overriding a variable with an operator => error") {
    val text =
      """---- MODULE const ----
        |VARIABLE n, m
        |OVERRIDE_n == m
        |A == {n}
        |================================
      """.stripMargin

    val (rootName, modules) =
      sanyImporter.loadFromSource("const", Source.fromString(text))
    val root = modules(rootName)
    assertThrows[OverridingError](new ConstAndDefRewriter(new IdleTracker())(root))
  }

  test("override an operator") {
    val text =
      """---- MODULE op ----
        |BoolMin(S) == CHOOSE x \in S: \A y \in S: x => y
        |OVERRIDE_BoolMin(S) == CHOOSE x \in S: TRUE
        |================================
      """.stripMargin

    val (rootName, modules) =
      sanyImporter.loadFromSource("op", Source.fromString(text))
    val root = modules(rootName)
    val rewritten = new ConstAndDefRewriter(new IdleTracker())(root)
    assert(rewritten.constDeclarations.isEmpty)
    assert(rewritten.operDeclarations.size == 1)
    val expected =
      TlaOperDecl("BoolMin", List(SimpleFormalParam("S")), tla.choose(tla.name("x"), tla.name("S"), tla.bool(true)))
    assert(expected == rewritten.operDeclarations.head)
  }

  test("override a unary operator with a binary operator") {
    val text =
      """---- MODULE op ----
        |BoolMin(S) == CHOOSE x \in S: \A y \in S: x => y
        |OVERRIDE_BoolMin(S, T) == CHOOSE x \in S: x \in T
        |================================
      """.stripMargin

    val (rootName, modules) =
      sanyImporter.loadFromSource("op", Source.fromString(text))
    val root = modules(rootName)
    assertThrows[OverridingError](new ConstAndDefRewriter(new IdleTracker())(root))
  }
}
