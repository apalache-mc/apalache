package at.forsyte.apalache.io

import at.forsyte.apalache.io.annotations.{Annotation, AnnotationBool, AnnotationStr, PrettyWriterWithAnnotations}
import at.forsyte.apalache.io.annotations.store.createAnnotationStore
import at.forsyte.apalache.tla.lir._
import UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import java.io.{PrintWriter, StringWriter}

@RunWith(classOf[JUnitRunner])
class TestPrettyWriterWithAnnotations extends FunSuite with BeforeAndAfterEach {
  private var stringWriter: StringWriter = _
  private var printWriter: PrintWriter = _

  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
  }

  test("variable declaration") {
    val decl = TlaVarDecl("myFun")
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("Int -> Bool")))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, 80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """(* @type: Int -> Bool; *)
        |VARIABLE myFun
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("constant declaration") {
    val decl = TlaConstDecl("N")
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("Int")), Annotation("sweet", AnnotationBool(true)))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, 80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """(* @type: Int; *)
        |(* @sweet(true) *)
        |CONSTANT N
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("operator declaration") {
    val decl = TlaOperDecl("MyOper", List(SimpleFormalParam("x"), SimpleFormalParam("y")), tla.bool(true))
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("(Int, Str) -> Bool")))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, 80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """(* @type: (Int, Str) -> Bool; *)
        |MyOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }
}
