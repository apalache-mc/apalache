package at.forsyte.apalache.io

import at.forsyte.apalache.io.annotations.{Annotation, AnnotationBool, AnnotationStr, PrettyWriterWithAnnotations}
import at.forsyte.apalache.io.annotations.store.createAnnotationStore
import at.forsyte.apalache.tla.lir._
import UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.io.lir.TextLayout
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import java.io.{PrintWriter, StringWriter}

@RunWith(classOf[JUnitRunner])
class TestPrettyWriterWithAnnotations extends FunSuite with BeforeAndAfterEach {
  private var stringWriter: StringWriter = _
  private var printWriter: PrintWriter = _
  private val layout80 = TextLayout().copy(textWidth = 80)

  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
  }

  test("variable declaration") {
    val decl = TlaVarDecl("myFun")
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("Int -> Bool")))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """VARIABLE
        |  (*
        |    @type: Int -> Bool;
        |  *)
        |  myFun
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("variable declaration without annotation") {
    val decl = TlaVarDecl("myFun")
    val store = createAnnotationStore()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """VARIABLE myFun
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("constant declaration") {
    val decl = TlaConstDecl("N")
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("Int")), Annotation("sweet", AnnotationBool(true)))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """CONSTANT
        |  (*
        |    @type: Int;
        |    @sweet(true)
        |  *)
        |  N
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("operator declaration") {
    val decl = TlaOperDecl("MyOper", List(OperParam("x"), OperParam("y")), tla.bool(true))
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("(Int, Str) -> Bool")))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """(*
        |  @type: (Int, Str) -> Bool;
        |*)
        |MyOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("recursive operator declaration") {
    val decl = TlaOperDecl("RecOper", List(OperParam("x"), OperParam("y")), tla.bool(true))
    decl.isRecursive = true
    val store = createAnnotationStore()
    store += decl.ID -> List(Annotation("type", AnnotationStr("(Int, Str) -> Bool")))

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """RECURSIVE RecOper(_, _)
        |(*
        |  @type: (Int, Str) -> Bool;
        |*)
        |RecOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("operator declaration without annotation") {
    val decl = TlaOperDecl("MyOper", List(OperParam("x"), OperParam("y")), tla.bool(true))
    val store = createAnnotationStore()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """MyOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("operator declaration with an empty list") {
    val decl = TlaOperDecl("MyOper", List(OperParam("x"), OperParam("y")), tla.bool(true))
    val store = createAnnotationStore()
    store += decl.ID -> List()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """MyOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }
}
