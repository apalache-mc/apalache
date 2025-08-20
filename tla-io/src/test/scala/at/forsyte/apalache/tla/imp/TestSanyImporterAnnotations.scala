package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.Annotation
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import org.junit.runner.RunWith
import org.scalatestplus.junit.JUnitRunner
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite

import scala.io.Source

/**
 * Tests on parsing annotations with the SANY importer.
 *
 * @author
 *   Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestSanyImporterAnnotations extends AnyFunSuite with BeforeAndAfter {
  private var sourceStore: SourceStore = _
  private var annotationStore: AnnotationStore = _
  private var sanyImporter: SanyImporter = _

  import at.forsyte.apalache.io.annotations.AnnotationArg._

  before {
    sourceStore = new SourceStore
    annotationStore = createAnnotationStore()
    sanyImporter = new SanyImporter(sourceStore, annotationStore)
  }

  private def loadModule(text: String): TlaModule = {
    val (rootName, modules) =
      sanyImporter.loadFromSource(Source.fromString(text))
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

    val module = loadModule(text)

    module.declarations.find(_.name == "S") match {
      case Some(d @ TlaConstDecl(_)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("awesome") :: Annotation(
            "type",
            mkStr("  Set(Int)  "),
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

    val module = loadModule(text)

    module.declarations.find(_.name == "S") match {
      case Some(d @ TlaVarDecl(_)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("amazing") :: Annotation(
            "type",
            mkStr(" Set(Int) "),
        ) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected a variable")
    }
  }

  test("operator with one big integer") {
    val text =
      """---- MODULE oper ----
        |\* 100000000000000000000
        |\* @type("Int");
        |X == 100000000000000000000
        |================================
      """.stripMargin

    val module = loadModule(text)

    module.declarations.find(_.name == "X") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("type", mkStr("Int"))
        assert(annotations.length == 2)
        // ignore the #freeText annotation
        assert(expected == annotations(1))

      case _ =>
        fail("Expected an operator")
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

    val module = loadModule(text)

    module.declarations.find(_.name == "Inc") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("pure") :: Annotation(
            "type",
            mkStr("Int => Int"),
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

    val module = loadModule(text)

    module.declarations.find(_.name == "A") match {
      // SanyImporter introduces a let-definition before application of a LOCAL operator
      case Some(TlaOperDecl(_, _, LetInEx(_, localDef))) =>
        val annotations = annotationStore(localDef.ID)
        val expected = Annotation("pure") :: Annotation(
            "type",
            mkStr("Int => Int"),
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

    val module = loadModule(text)

    module.declarations.find(_.name == "A") match {
      case Some(TlaOperDecl(_, _, LetInEx(_, incDecl))) =>
        val annotations = annotationStore(incDecl.ID)
        val expected = Annotation("pure") :: Annotation(
            "type",
            mkStr("Int => Int"),
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

    val module = loadModule(text)

    module.declarations.find(_.name == "Fact") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("tailrec") :: Annotation(
            "type",
            mkStr("Int => Int"),
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

    val module = loadModule(text)

    module.declarations.find(_.name == "Fact") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = Annotation("type", mkStr("Int -> Int")) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }

  test("missing semicolon") {
    // regression for #954
    val text =
      """-------- MODULE missing ------------
        |\* last action performed
        |\* @type: ACTION
        |action == TRUE
        |================================
      """.stripMargin

    // as explained in #1292, we are not throwing an exception anymore
    val module = loadModule(text)

    val action = module.declarations
      .find(_.name == "action")
      .getOrElse(fail("Expected an operator"))
    val annotations = annotationStore(action.ID)
    assert(annotations.length == 1)
  }

  test("corner cases") {
    val text =
      """-------- MODULE corner ------------
        |(*
        |  this annotation finishes with \n
        |  @withlinefeed
        | *)
        |(* this annotation finishes at the end of the comment
        |  @withstar*)
        |\* this annotation finishes at the end of the comment string!
        |\* @witheof
        |Corner == TRUE
        |================================
      """.stripMargin

    val module = loadModule(text)

    module.declarations.find(_.name == "Corner") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        assert(annotations.length == 4)
        // the head is #freeText, which we don't care about
        assert(Annotation("withlinefeed") == annotations(1))
        assert(Annotation("withstar") == annotations(2))
        assert(Annotation("witheof") == annotations(3))

      case _ =>
        fail("Expected an operator")
    }
  }

  test("line breaks are preserved inside type annotations") {
    // Required to allow identifying and parsing out one-line comments inside of type annotations
    // See https://github.com/apalache-mc/apalache/issues/2162
    val text =
      """----- MODULE OneLineComments -----
        |
        | CONSTANT
        | \* @type: {
        | \*   //  comment in single-line annotation
        | \*   f : Int
        | \* };
        |   singleLine,
        | (* @type: {
        |      //  comment in multi-line annotation
        |      g : Int
        |   }; *)
        |   multiLine
        |=====
      """.stripMargin
    val module = loadModule(text)

    val expectedSingleLine =
      """{
        | // comment in single-line annotation
        | f : Int
        | }""".stripMargin
    val expectedMultiLine =
      """{
        | // comment in multi-line annotation
        | g : Int
        | }""".stripMargin
    module.declarations.filter(_.name.endsWith("Line")).map {
      case d @ TlaConstDecl(_) =>
        val annotation :: _ = annotationStore(d.ID)
        if (d.name == "singleLine") {
          assert(Annotation("type", mkStr(expectedSingleLine)) == annotation)
        } else {
          assert(Annotation("type", mkStr(expectedMultiLine)) == annotation)
        }

      case _ =>
        fail("Expected a constant")
    }
  }
}
