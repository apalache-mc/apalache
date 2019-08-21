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

  test("name") {
    val writer = new PrettyWriter2(printWriter, 80)
    writer.write(tla.name("awesome"))
    printWriter.flush()
    val result = stringWriter.toString
    assert("awesome" == result)
  }

  test("one-line set") {
    val writer = new PrettyWriter2(printWriter, 80)
    writer.write(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    printWriter.flush()
    val result = stringWriter.toString
    assert("{ 1, 2, 3 }" == result)
  }

  test("multi-line set") {
    val writer = new PrettyWriter2(printWriter, 20)
    writer.write(tla.enumSet(1.to(10).map(tla.int) :_*))
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """{
        |  1, 2, 3, 4, 5, 6, 7,
        |  8, 9, 10
        |}""".stripMargin
    assert(expected == result)
  }

  test("one-line conjunction") {
    val writer = new PrettyWriter2(printWriter, 80)
    val expr = tla.and(1.to(3) map(_ => tla.name("verylongname")) :_*)
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """verylongname /\ verylongname /\ verylongname""".stripMargin
    assert(expected == result)
  }

  test("multi-line conjunction") {
    val writer = new PrettyWriter2(printWriter, 40)
    val expr = tla.impl(tla.bool(true), tla.and(1.to(5) map(_ => tla.name("verylongname")) :_*))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """TRUE
        |  => verylongname
        |    /\ verylongname
        |    /\ verylongname
        |    /\ verylongname
        |    /\ verylongname""".stripMargin
    assert(expected == result)
  }

  test("nested multiline conjunction/disjunction") {
    val writer = new PrettyWriter2(printWriter, 80)
    val or = tla.or(1.to(3) map(_ => tla.name("verylongname")) :_*)
    val and = tla.and(1.to(3) map (_ => or) :_*)
    writer.write(and)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """(verylongname \/ verylongname \/ verylongname)
        |    /\ (verylongname \/ verylongname \/ verylongname)
        |    /\ (verylongname \/ verylongname \/ verylongname)""".stripMargin
    assert(expected == result)
  }

  test("nested multiline conjunction under negation") {
    val writer = new PrettyWriter2(printWriter, 20)
    val and = tla.and(1.to(3) map(_ => tla.name("verylongname")) :_*)
    writer.write(tla.not(and))
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """¬(verylongname
        |      /\ verylongname
        |      /\ verylongname)""".stripMargin
    assert(expected == result)
  }

  test("one-line exists") {
    val writer = new PrettyWriter2(printWriter, 40)
    val expr =
      tla.exists(tla.name("x"),
        tla.name("y"), tla.name("z"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected ="∃x ∈ y: z"
    assert(expected == result)
  }

  test("multi-line exists") {
    val writer = new PrettyWriter2(printWriter, 40)
    val expr =
      tla.exists(tla.name("verylongname1"),
        tla.name("verylongname2"), tla.name("verylongname3"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """∃verylongname1 ∈ verylongname2:
        |  verylongname3""".stripMargin
    assert(expected == result)
  }

  test("nested quantifiers") {
    val writer = new PrettyWriter2(printWriter, 40)
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
      """∀verylong4 ∈ verylong5:
        |  ∃verylongname1 ∈ verylongname2:
        |    verylongname3""".stripMargin
    assert(expected == result)
  }

  test("a one-line record") {
    val writer = new PrettyWriter2(printWriter, 40)
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
    val writer = new PrettyWriter2(printWriter, 40)
    val expr = tla.enumFun(
      tla.name("verylong1"), tla.name("verylong2"),
      tla.name("verylong3"), tla.name("verylong4"),
      tla.name("verylong5"), tla.name("verylong6")
    ) ////
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[verylong1 ↦ verylong2,
        |  verylong3 ↦ verylong4,
        |  verylong5 ↦ verylong6]""".stripMargin
    assert(expected == result)
  }

  test("a narrow multi-line record") {
    val writer = new PrettyWriter2(printWriter, 20)
    val expr = tla.enumFun(
      tla.name("verylong1"), tla.name("verylong2"),
      tla.name("verylong3"), tla.name("verylong4"),
      tla.name("verylong5"), tla.name("verylong6")
    ) ////
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[verylong1 ↦
        |    verylong2,
        |  verylong3 ↦
        |    verylong4,
        |  verylong5 ↦
        |    verylong6]""".stripMargin
    assert(expected == result)
  }

  test("a one-line function") {
    val writer = new PrettyWriter2(printWriter, 80)
    val expr = tla.funDef(tla.plus(tla.name("x"), tla.name("y")),
      tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[ x ∈ S, y ∈ T ↦ x + y ]""".stripMargin
    assert(expected == result)
  }

  test("a multi-line function") {
    val writer = new PrettyWriter2(printWriter, 30)
    val expr = tla.funDef(tla.plus(tla.name("verylong1"), tla.name("verylong2")),
      tla.name("verylong1"), tla.name("verylong3"),
      tla.name("verylong2"), tla.name("verylong4"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[
        |  verylong1 ∈ verylong3,
        |  verylong2 ∈ verylong4 ↦
        |    verylong1 + verylong2
        |]""".stripMargin
    assert(expected == result)
  }

  test("a one-line map") {
    val writer = new PrettyWriter2(printWriter, 80)
    val expr = tla.map(tla.plus(tla.name("x"), tla.name("y")),
      tla.name("x"), tla.name("S"), tla.name("y"), tla.name("T"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """{ x + y: x ∈ S, y ∈ T }""".stripMargin
    assert(expected == result)
  }

  test("a multi-line map") {
    val writer = new PrettyWriter2(printWriter, 30)
    val expr = tla.map(tla.plus(tla.name("verylong1"), tla.name("verylong2")),
      tla.name("verylong1"), tla.name("verylong3"),
      tla.name("verylong2"), tla.name("verylong4"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """{
        |  verylong1 + verylong2:
        |    verylong1 ∈ verylong3,
        |    verylong2 ∈ verylong4
        |}""".stripMargin
    assert(expected == result)
  }

  test("a one-line function application") {
    val writer = new PrettyWriter2(printWriter, 80)
    val expr = tla.appFun(tla.name("f"), tla.name("e"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected = """f[e]""".stripMargin
    assert(expected == result)
  }

  test("a multi-line function application") {
    val writer = new PrettyWriter2(printWriter, 20)
    val expr = tla.appFun(tla.name("verylongname1"), tla.name("verylongname2"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """verylongname1[
        |  verylongname2
        |]""".stripMargin
    assert(expected == result)
  }

  test("a one-line IF-THEN-ELSE") {
    val writer = new PrettyWriter2(printWriter, 80)
    val expr = tla.ite(tla.name("a"), tla.name("b"), tla.name("c"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected = """IF a THEN b ELSE c""".stripMargin
    assert(expected == result)
  }

  test("a multi-line IF-THEN-ELSE") {
    val writer = new PrettyWriter2(printWriter, 20)
    val expr = tla.ite(tla.name("verylongname1"),
      tla.name("verylongname2"),
      tla.name("verylongname3"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """IF verylongname1
        |THEN verylongname2
        |ELSE verylongname3""".stripMargin
    assert(expected == result)
  }

  test("a one-line EXCEPT") {
    val writer = new PrettyWriter2(printWriter, 80)
    val expr = tla.except(tla.name("f"), tla.name("k"), tla.name("v"))
    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected = """[ f EXCEPT ![k] = v ]""".stripMargin
    assert(expected == result)
  }

  test("a multi-line EXCEPT") {
    val writer = new PrettyWriter2(printWriter, 40)
    val expr = tla.except(
      tla.name("verylongname1"),
      tla.name("verylongname2"),
      tla.name("verylongname3")
    ) ///

    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[
        |  verylongname1 EXCEPT
        |    ![verylongname2] = verylongname3
        |]""".stripMargin
    assert(expected == result)
  }

  test("a monster EXCEPT") {
    val writer = new PrettyWriter2(printWriter, 40)
    val expr = tla.except(
      tla.name("verylongname1"),
      tla.name("verylongname2"),
      tla.name("verylongname3"),
      tla.name("verylongname4"),
      tla.name("verylongname5")
    ) ///

    writer.write(expr)
    printWriter.flush()
    val result = stringWriter.toString
    val expected =
      """[
        |  verylongname1 EXCEPT
        |    ![verylongname2] = verylongname3,
        |    ![verylongname4] = verylongname5
        |]""".stripMargin
    assert(expected == result)
  }
}

