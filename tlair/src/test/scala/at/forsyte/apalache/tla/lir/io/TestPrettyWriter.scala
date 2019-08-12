package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner

import at.forsyte.apalache.tla.lir.convenience.tla

@RunWith( classOf[JUnitRunner] )
class TestPrettyWriter extends FunSuite with BeforeAndAfterEach {
  private var stringWriter = new StringWriter()
  private var printWriter = new PrintWriter(stringWriter)


  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
  }

  test("one-line set") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    printWriter.flush()
    val result = stringWriter.toString
    assert("{ 1, 2, 3 }" == result)
  }

  test("multi-line set") {
    val writer = new PrettyWriter(printWriter, 20)
    writer.write(tla.enumSet(1.to(10).map(tla.int) :_*))
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """{ $
        |  1, 2, 3, 4, 5, 6, $
        |  7, 8, 9, 10 }""".stripMargin.replaceAll("\\$", "")
    assert(expected == result)
  }

  test("one-line conjunction") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = tla.and(1.to(4) map(_ => tla.name("verylongname")) :_*)
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """(verylongname /\ verylongname /\ verylongname /\ verylongname)""".stripMargin
    assert(expected == result)
  }

  test("multi-line conjunction") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = tla.and(1.to(5) map(_ => tla.name("verylongname")) :_*)
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """
        |/\ verylongname
        |/\ verylongname
        |/\ verylongname
        |/\ verylongname
        |/\ verylongname""".stripMargin
    assert(expected == result)
  }

  test("nested multiline conjunction/disjunction") {
    val writer = new PrettyWriter(printWriter, 80)
    val or = tla.or(1.to(3) map(_ => tla.name("verylongname")) :_*)
    val and = tla.and(1.to(3) map (_ => or) :_*)
    writer.write(and)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """
        |/\ (verylongname \/ verylongname \/ verylongname)
        |/\ (verylongname \/ verylongname \/ verylongname)
        |/\ (verylongname \/ verylongname \/ verylongname)""".stripMargin
    assert(expected == result)
  }

  test("nested multiline conjunction/disjunction with indentation") {
    val writer = new PrettyWriter(printWriter, 40)
    val or = tla.or(1.to(3) map(_ => tla.name("verylongname")) :_*)
    val and = tla.and(1.to(3) map (_ => or) :_*)
    writer.write(and)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """
        |/\ $
        |  \/ verylongname
        |  \/ verylongname
        |  \/ verylongname
        |/\ $
        |  \/ verylongname
        |  \/ verylongname
        |  \/ verylongname
        |/\ $
        |  \/ verylongname
        |  \/ verylongname
        |  \/ verylongname""".stripMargin.replaceAll("\\$", "")
    assert(expected == result)
  }
}

