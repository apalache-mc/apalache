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
        |  1, 2, 3, 4, 5, 6, 7, $
        |  8, 9, 10 }""".stripMargin.replaceAll("\\$", "")
    assert(expected == result)
  }

  test("one-line conjunction") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = tla.and(1.to(4) map(_ => tla.name("verylongname")) :_*)
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """verylongname /\ verylongname /\ verylongname /\ verylongname""".stripMargin
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
      """verylongname /\ verylongname
        |   /\ verylongname /\ verylongname
        |   /\ verylongname""".stripMargin
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
      """(verylongname \/ verylongname \/ verylongname)
        |   /\ (verylongname \/ verylongname \/ verylongname)
        |   /\ (verylongname \/ verylongname \/ verylongname)""".stripMargin
    assert(expected == result)
  }

  test("nested multiline conjunction under negation") {
    val writer = new PrettyWriter(printWriter, 20)
    val and = tla.and(1.to(3) map(_ => tla.name("verylongname")) :_*)
    writer.write(tla.not(and))
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """~(verylongname
        |   /\ verylongname
        |   /\ verylongname)""".stripMargin
    assert(expected == result)
  }

  test("multi-line exists") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr =
      tla.exists(tla.name("verylongname1"),
        tla.name("verylongname2"), tla.name("verylongname3"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """∃verylongname1 ∈ verylongname2: $
        |  verylongname3"""
        .stripMargin.replaceAll("\\$", "")
    assert(expected == result)
  }

  test("nested quantifiers") {
    val writer = new PrettyWriter(printWriter, 40)
    val ex1 =
      tla.exists(tla.name("verylongname1"),
        tla.name("verylongname2"), tla.name("verylongname3"))
    val ex2 =
      tla.forall(tla.name("verylong4"), tla.name("verylong5"), ex1)
    writer.write(ex2)
    printWriter.flush()
    val result = stringWriter.toString
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """∀verylong4 ∈ verylong5: $
        |  ∃verylongname1 ∈ verylongname2: $
        |    verylongname3"""
        .stripMargin.replaceAll("\\$", "")
    assert(expected == result)
  }

  test("a one-line record") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = tla.enumFun(
      tla.name("x1"), tla.name("x2"),
      tla.name("x3"), tla.name("x4"),
      tla.name("x5"), tla.name("x6")
    ) ////
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[x1 ↦ x2, x3 ↦ x4, x5 ↦ x6]""".stripMargin
    assert(expected == result)
  }

  test("a multi-line record") {
    val writer = new PrettyWriter(printWriter, 20)
    val expr = tla.enumFun(
      tla.name("verylong1"), tla.name("verylong2"),
      tla.name("verylong3"), tla.name("verylong4"),
      tla.name("verylong5"), tla.name("verylong6")
    ) ////
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """~(verylongname
        |   /\ verylongname
        |   /\ verylongname)""".stripMargin
    assert(expected == result)
  }
}

