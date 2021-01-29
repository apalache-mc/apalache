package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.Annotation
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfter, FunSuite}

import scala.io.Source

/**
 * Tests on parsing annotations with the SANY importer.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestSanyImporterAnnotations extends FunSuite with BeforeAndAfter {
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _

  import at.forsyte.apalache.io.annotations.TlaAnnotationArg._

  before {
    sourceStore = new SourceStore
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
  }

  private def loadModule(text: String, moduleName: String): TlaModule = {
    val (rootName, modules) =
      sanyImporter.loadFromSource(moduleName, Source.fromString(text))
    modules(rootName)
  }

  test("one constant") {
    val text =
      """---- MODULE oneconst ----
        |CONSTANT
        | (*
        |    @awesome
        |    @type("  Set(Int)  ")
        |  *)
        |  S
        |================================
      """.stripMargin

    val module = loadModule(text, "oneconst")

    module.declarations.find(_.name == "S") match {
      case Some(d @ TlaConstDecl(_)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("awesome") :: Annotation(
            "type",
            mkStr("  Set(Int)  ")
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected a constant")
    }
  }

  test("one variable") {
    val text =
      """---- MODULE onevar ----
        |VARIABLE
        |  \* @amazing
        |  \* @type(" Set(Int) ")
        |  S
        |================================
      """.stripMargin

    val module = loadModule(text, "onevar")

    module.declarations.find(_.name == "S") match {
      case Some(d @ TlaVarDecl(_)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("amazing") :: Annotation(
            "type",
            mkStr(" Set(Int) ")
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected a variable")
    }
  }

  test("annotated operator") {
    val text =
      """---- MODULE oper ----
        |EXTENDS Integers
        |(*
        |   @pure
        |   @type("Int => Int")
        |*)
        |Inc(x) == x + 1
        |================================
      """.stripMargin

    val module = loadModule(text, "oper")

    module.declarations.find(_.name == "Inc") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("pure") :: Annotation(
            "type",
            mkStr("Int => Int")
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }

  test("annotated local operator") {
    // in contrast to LET-IN and RECURSIVE, the comment annotations for local operators should come before
    // the keyword LOCAL. Need to figure that with Markus.
    val text =
      """---- MODULE oper ----
        |EXTENDS Integers
        |
        |(*
        |   @pure
        |   @type("Int => Int")
        |*)
        |LOCAL Inc(x) == x + 1
        |
        |A(n) == Inc(n)
        |================================
      """.stripMargin

    val module = loadModule(text, "oper")

    module.declarations.find(_.name == "A") match {
      // SanyImporter introduces a let-definition before application of a LOCAL operator
      case Some(d @ TlaOperDecl(_, _, LetInEx(_, localDef))) =>
        val annotations = annotationStore(localDef.ID)
        val expected = Annotation("pure") :: Annotation(
            "type",
            mkStr("Int => Int")
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }

  test("annotated LET-IN operator") {
    // Similar to recursive operators,
    // it is probably unexpected that the annotation comes after the LET keyword, not before it.
    // The reason is that you can define multiple operators in a single LET-definition.
    val text =
      """---- MODULE oper ----
        |EXTENDS Integers
        |
        |A(n) ==
        |  LET
        |  (*
        |    @pure
        |    @type("Int => Int")
        |  *)
        |  Inc(x) == x + 1 IN
        |  Inc(n)
        |================================
      """.stripMargin

    val module = loadModule(text, "oper")

    module.declarations.find(_.name == "A") match {
      case Some(d @ TlaOperDecl(_, _, LetInEx(_, incDecl))) =>
        val annotations = annotationStore(incDecl.ID)
        val expected = Annotation("pure") :: Annotation(
            "type",
            mkStr("Int => Int")
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }

  test("annotated recursive operator") {
    // recursive operators are tricky: The annotations should be right before the operator definition,
    // not before the RECURSIVE keyword!
    val text =
      """-------- MODULE oper ------------
        |EXTENDS Integers
        |
        |RECURSIVE Fact(_)
        |(*
        |   @tailrec
        |   @type("Int => Int")
        |*)
        |Fact(n) ==
        |  IF n <= 1 THEN 1 ELSE n * Fact(n - 1)
        |================================
      """.stripMargin

    val module = loadModule(text, "oper")

    module.declarations.find(_.name == "Fact") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("tailrec") :: Annotation(
            "type",
            mkStr("Int => Int")
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }

  test("annotated recursive function") {
    val text =
      """-------- MODULE fun ------------
        |EXTENDS Integers
        |
        |(*
        |   @type("Int -> Int")
        |*)
        |Fact[n \in Int] ==
        |  IF n <= 1 THEN 1 ELSE n * Fact[n - 1]
        |================================
      """.stripMargin

    val module = loadModule(text, "fun")

    module.declarations.find(_.name == "Fact") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("type", mkStr("Int -> Int")) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }

  test("annotated non-recursive function") {
    val text =
      """-------- MODULE fun ------------
        |EXTENDS Integers
        |
        |(*
        |   @type("Int -> Int")
        |*)
        |Inc[n \in Int] == n + 1
        |================================
      """.stripMargin

    val module = loadModule(text, "fun")

    module.declarations.find(_.name == "Inc") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("type", mkStr("Int -> Int")) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }
}
