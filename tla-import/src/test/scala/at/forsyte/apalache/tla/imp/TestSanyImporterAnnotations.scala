package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.io.annotations.TlaAnnotation
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
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
  private var annotationStore: TlaAnnotationStore = _
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
        val expected = TlaAnnotation("awesome") :: TlaAnnotation("type", mkStr("  Set(Int)  ")) :: Nil
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
        val expected = TlaAnnotation("amazing") :: TlaAnnotation("type", mkStr(" Set(Int) ")) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected a variable")
    }
  }

  /*
  test("annotated operator") {
    val text =
      """---- MODULE oper ----
        |EXTENDS Integers
        |(*
        |@awesome
        |@type("Int => Int")
        |*)
        |Inc(x) == x + 1
        |================================
      """.stripMargin

    val module = loadModule(text, "oper")

    module.declarations.find(_.name == "Inc") match {
      case Some(d @ TlaOperDecl(_, _, _)) =>
        val annotations = annotationStore(d.ID)
        val expected = TlaAnnotation("awesome") :: TlaAnnotation("type", mkStr("Int => Int")) :: Nil
        assert(expected == annotations)

      case _ =>
        fail("Expected an operator")
    }
  }
   */
}
