package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir.{OperEx, SimpleFormalParam, TlaOperDecl}
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.convenience.tla._

@RunWith(classOf[JUnitRunner])
class TestPrettyWriter extends FunSuite with BeforeAndAfterEach {
  private var stringWriter = new StringWriter()
  private var printWriter = new PrintWriter(stringWriter)


  override protected def beforeEach(): Unit = {
    stringWriter = new StringWriter()
    printWriter = new PrintWriter(stringWriter)
  }

  test("name") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(name("awesome"))
    printWriter.flush()
    assert("awesome" == stringWriter.toString)
  }

  test("ENABLED and prime") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(enabled(prime("x")))
    printWriter.flush()
    assert("ENABLED x'" == stringWriter.toString)
  }

  test("UNCHANGED") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(unchanged("x"))
    printWriter.flush()
    assert("UNCHANGED x" == stringWriter.toString)
  }

  test("[A]_vars") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(stutt("A", "vars"))
    printWriter.flush()
    assert("[A]_vars" == stringWriter.toString)
  }

  test("<A>_vars") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(nostutt("A", "vars"))
    printWriter.flush()
    assert("<A>_vars" == stringWriter.toString)
  }

  test("A \\cdot B") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(comp("A", "B"))
    printWriter.flush()
    assert("A \\cdot B" == stringWriter.toString)
  }

  test("WF_vars(A)") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(WF("vars", "A"))
    printWriter.flush()
    assert("WF_vars(A)" == stringWriter.toString)
  }

  test("SF_vars(A)") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(SF("vars", "A"))
    printWriter.flush()
    assert("SF_vars(A)" == stringWriter.toString)
  }

  test("[]A") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(box("A"))
    printWriter.flush()
    assert("[]A" == stringWriter.toString)
  }

  test("<>A") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(diamond("A"))
    printWriter.flush()
    assert("<>A" == stringWriter.toString)
  }

  test("A ~> B") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(leadsTo("A", "B"))
    printWriter.flush()
    assert("A ~> B" == stringWriter.toString)
  }

  test("A -+-> B") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(guarantees("A", "B"))
    printWriter.flush()
    assert("A -+-> B" == stringWriter.toString)
  }

  test("empty set") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(enumSet())
    printWriter.flush()
    assert("{}" == stringWriter.toString)
  }

  test("singleton set") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(enumSet(42))
    printWriter.flush()
    assert("{42}" == stringWriter.toString)
  }

  test("one-line set") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(enumSet(int(1), int(2), int(3)))
    printWriter.flush()
    assert("{ 1, 2, 3 }" == stringWriter.toString)
  }

  test("multi-line set") {
    val writer = new PrettyWriter(printWriter, 20)
    writer.write(enumSet(1.to(10).map(int): _*))
    printWriter.flush()
    val expected =
      """{
        |  1, 2, 3, 4, 5, 6, 7,
        |  8, 9, 10
        |}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("one-line tuple") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(tuple(1, 2, 3))
    printWriter.flush()
    assert("<<1, 2, 3>>" == stringWriter.toString)
  }

  test("multi-line tuple") {
    val writer = new PrettyWriter(printWriter, 20)
    writer.write(tuple(1.to(10).map(int): _*))
    printWriter.flush()
    val expected =
      """<<
        |  1, 2, 3, 4, 5, 6, 7,
        |  8, 9, 10
        |>>""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("one-line Cartesian product") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(times("X", "Y", "Z"))
    printWriter.flush()
    assert("X \\X Y \\X Z" == stringWriter.toString)
  }

  test("multi-line Cartesian product") {
    val writer = new PrettyWriter(printWriter, 40)
    writer.write(times("verylongname1", "verylongname2", "verylongname3"))
    printWriter.flush()
    val expected =
      """verylongname1
        |  \X verylongname2
        |  \X verylongname3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("one-line conjunction") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = and(1.to(3) map (_ => name("verylongname")): _*)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """verylongname /\ verylongname /\ verylongname""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("multi-line conjunction") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = impl(true, and(1.to(5) map (_ => name("verylongname")): _*))
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """TRUE
        |  => verylongname
        |    /\ verylongname
        |    /\ verylongname
        |    /\ verylongname
        |    /\ verylongname""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested multiline conjunction/disjunction") {
    val writer = new PrettyWriter(printWriter, 80)
    val orEx = or(1.to(3) map (_ => name("verylongname")): _*)
    val andEx = and(1.to(3) map (_ => orEx): _*)
    writer.write(andEx)
    printWriter.flush()
    val expected =
      """(verylongname \/ verylongname \/ verylongname)
        |  /\ (verylongname \/ verylongname \/ verylongname)
        |  /\ (verylongname \/ verylongname \/ verylongname)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested multiline conjunction under negation") {
    val writer = new PrettyWriter(printWriter, 20)
    val andEx = and(1.to(3) map (_ => name("verylongname")): _*)
    writer.write(not(andEx))
    printWriter.flush()
    val expected =
      """~(verylongname
        |  /\ verylongname
        |  /\ verylongname)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("one-line exists") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = exists("x", "y", "z")
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected = "\\E x \\in y: z"
    assert(expected == stringWriter.toString)
  }

  test("multi-line exists") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr =
      exists("verylongname1", "verylongname2", "verylongname3")
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """\E verylongname1 \in verylongname2:
        |  verylongname3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested quantifiers") {
    val writer = new PrettyWriter(printWriter, 40)
    val ex1 =
      exists("verylongname1", "verylongname2", "verylongname3")
    val ex2 =
      forall("verylong4", "verylong5", ex1)
    writer.write(ex2)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """\A verylong4 \in verylong5:
        |  \E verylongname1 \in verylongname2:
        |    verylongname3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested \\EE and \\AA") {
    val writer = new PrettyWriter(printWriter, 10)
    val ex1 =
      EE("verylongname1", "verylongname2")
    val ex2 =
      AA("verylong3", ex1)
    writer.write(ex2)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected =
      """\AA verylong3:
        |  \EE verylongname1:
        |    verylongname2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line record") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = enumFun(
      "x1", "x2",
      "x3", "x4",
      "x5", "x6"
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[x1 |-> x2, x3 |-> x4, x5 |-> x6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line record") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = enumFun(
      "verylong1", "verylong2",
      "verylong3", "verylong4",
      "verylong5", "verylong6"
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[verylong1 |-> verylong2,
        |  verylong3 |-> verylong4,
        |  verylong5 |-> verylong6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a narrow multi-line record") {
    val writer = new PrettyWriter(printWriter, 20)
    val expr = enumFun(
      "verylong1", "verylong2",
      "verylong3", "verylong4",
      "verylong5", "verylong6"
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[verylong1 |->
        |    verylong2,
        |  verylong3 |->
        |    verylong4,
        |  verylong5 |->
        |    verylong6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line set of records") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = recSet(
      "x1", "x2",
      "x3", "x4",
      "x5", "x6"
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[x1: x2, x3: x4, x5: x6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line set of records") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = recSet(
      "verylong1", "verylong2",
      "verylong3", "verylong4",
      "verylong5", "verylong6"
    ) ////
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[verylong1: verylong2,
        |  verylong3: verylong4,
        |  verylong5: verylong6]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line function") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = funDef(plus("x", "y"),
      "x", "S", "y", "T")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[ x \in S, y \in T |-> x + y ]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line function") {
    val writer = new PrettyWriter(printWriter, 30)
    val expr = funDef(plus("verylong1", "verylong2"),
      "verylong1", "verylong3",
      "verylong2", "verylong4")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[
        |  verylong1 \in verylong3,
        |  verylong2 \in verylong4 |->
        |    verylong1 + verylong2
        |]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line map") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = map(plus("x", "y"),
      "x", "S", "y", "T")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{ x + y: x \in S, y \in T }""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line map") {
    val writer = new PrettyWriter(printWriter, 30)
    val expr = map(plus("verylong1", "verylong2"),
      "verylong1", "verylong3",
      "verylong2", "verylong4")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{
        |  verylong1 + verylong2:
        |    verylong1 \in verylong3,
        |    verylong2 \in verylong4
        |}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line filter") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = filter("x", "S", "P")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{ x \in S: P }""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("precedence in filter") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = filter("x", "S", lt("x", 5))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{ x \in S: x < 5 }""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line filter") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = filter(
      "verylongname1",
      "verylongname2",
      "verylongname3")

    writer.write(expr)
    printWriter.flush()
    val expected =
      """{
        |  verylongname1 \in verylongname2:
        |    verylongname3
        |}""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line function application") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = appFun("f", "e")
    writer.write(expr)
    printWriter.flush()
    val expected = """f[e]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line function application") {
    val writer = new PrettyWriter(printWriter, 20)
    val expr = appFun("verylongname1", "verylongname2")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """verylongname1[
        |  verylongname2
        |]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line IF-THEN-ELSE") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = ite("a", "b", "c")
    writer.write(expr)
    printWriter.flush()
    val expected = """IF a THEN b ELSE c""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line IF-THEN-ELSE") {
    val writer = new PrettyWriter(printWriter, 20)
    val expr = ite("verylongname1",
      "verylongname2",
      "verylongname3")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """IF verylongname1
        |THEN verylongname2
        |ELSE verylongname3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line EXCEPT") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = except("f", "k", "v")
    writer.write(expr)
    printWriter.flush()
    val expected = """[ f EXCEPT ![k] = v ]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line EXCEPT") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = except(
      "verylongname1",
      "verylongname2",
      "verylongname3"
    ) ///

    writer.write(expr)
    printWriter.flush()
    val expected =
      """[
        |  verylongname1 EXCEPT
        |    ![verylongname2] = verylongname3
        |]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a monster EXCEPT") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = except(
      "verylongname1",
      "verylongname2",
      "verylongname3",
      "verylongname4",
      "verylongname5"
    ) ///

    writer.write(expr)
    printWriter.flush()
    val expected =
      """[
        |  verylongname1 EXCEPT
        |    ![verylongname2] = verylongname3,
        |    ![verylongname4] = verylongname5
        |]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("Cardinality") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = card("S")
    writer.write(expr)
    printWriter.flush()
    val expected = """Cardinality(S)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("<<a>> \\o <<b>>") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = concat(tuple("a"), tuple("b"))
    writer.write(expr)
    printWriter.flush()
    val expected = """<<a>> \o <<b>>""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("Append(<<a>>, b)") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = append(tuple("a"), "b")
    writer.write(expr)
    printWriter.flush()
    val expected = """Append(<<a>>, b)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line CASE") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = caseSplit("guard1", "action1", "guard2", "action2")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1 -> action1
        |  [] guard2 -> action2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a concise multi-line CASE") {
    val writer = new PrettyWriter(printWriter, 15)
    val expr = caseSplit("guard1", "action1", "guard2", "action2")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1
        |    -> action1
        |  [] guard2
        |    -> action2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line CASE with OTHER") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = caseOther("otherAction", "guard1", "action1", "guard2", "action2")
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1 -> action1
        |  [] guard2 -> action2
        |  [] OTHER -> otherAction""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = letIn("A", TlaOperDecl("A", List(), 1))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LET A == 1 IN A""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val decl =
      TlaOperDecl("AVeryLongName",
        List(SimpleFormalParam("param1"), SimpleFormalParam("param2")),
        plus("param1", "param2"))
    val expr = letIn(OperEx(decl.operator, 1, 2), decl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LET AVeryLongName(param1, param2) ==
        |  param1 + param2
        |IN
        |AVeryLongName(1, 2)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("multiple definitions in LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val decl1 =
      TlaOperDecl("AVeryLongName",
        List(SimpleFormalParam("param1"), SimpleFormalParam("param2")),
        plus("param1", "param2"))
    val decl2 =
      TlaOperDecl("BVeryLongName",
        List(SimpleFormalParam("param1"), SimpleFormalParam("param2")),
        plus("param1", "param2"))
    val expr = letIn(
      mult(OperEx(decl1.operator, 1, 2),
      OperEx(decl2.operator, 3, 4)),
      decl1, decl2)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LET AVeryLongName(param1, param2) ==
        |  param1 + param2
        |IN
        |LET BVeryLongName(param1, param2) ==
        |  param1 + param2
        |IN
        |AVeryLongName(1, 2)
        |  * BVeryLongName(3, 4)""".stripMargin
    assert(expected == stringWriter.toString)
  }
}

