package at.forsyte.apalache.io

import at.forsyte.apalache.io.annotations.PrettyWriterWithAnnotations
import at.forsyte.apalache.io.annotations.store.createAnnotationStore
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.io.lir.TextLayout
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{BeforeAndAfterEach, FunSuite}

import java.io.{PrintWriter, StringWriter}

@RunWith(classOf[JUnitRunner])
class TestPrettyWriterWithTypes extends FunSuite with BeforeAndAfterEach {
  private var stringWriter: StringWriter = _
  private var printWriter: PrintWriter = _
  private val layout80 = TextLayout().copy(textWidth = 80)

  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
  }

  test("variable declaration") {
    val decl = TlaVarDecl("myFun").withTag(Typed(FunT1(IntT1(), BoolT1())))
    val store = createAnnotationStore()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """VARIABLE
        |  (*
        |    @type: (Int -> Bool);
        |  *)
        |  myFun
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("constant declaration") {
    val decl = TlaConstDecl("N").withTag(Typed(IntT1()))
    val store = createAnnotationStore()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """CONSTANT
        |  (*
        |    @type: Int;
        |  *)
        |  N
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("operator declaration") {
    val decl = TlaOperDecl("MyOper", List(OperParam("x"), OperParam("y")), tla.bool(true))
      .withTag(Typed(OperT1(Seq(IntT1(), StrT1()), BoolT1())))
    val store = createAnnotationStore()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """(*
        |  @type: ((Int, Str) => Bool);
        |*)
        |MyOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("recursive operator declaration") {
    val decl = TlaOperDecl("RecOper", List(OperParam("x"), OperParam("y")), tla.bool(true))
      .withTag(Typed(OperT1(Seq(IntT1(), StrT1()), BoolT1())))
    decl.isRecursive = true
    val store = createAnnotationStore()

    val writer = new PrettyWriterWithAnnotations(store, printWriter, layout80)
    writer.write(decl)
    printWriter.flush()
    val expected =
      """RECURSIVE RecOper(_, _)
        |(*
        |  @type: ((Int, Str) => Bool);
        |*)
        |RecOper(x, y) == TRUE
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }
}
