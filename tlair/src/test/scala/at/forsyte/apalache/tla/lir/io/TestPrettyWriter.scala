package at.forsyte.apalache.tla.lir.io

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.{BeforeAndAfterEach, FunSuite}
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.UntypedPredefs._

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

  test("apply A") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(OperEx(TlaOper.apply, name("A")))
    printWriter.flush()
    assert("A" == stringWriter.toString)
  }

  test("apply A to 1") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(OperEx(TlaOper.apply, name("A"), int(1)))
    printWriter.flush()
    assert("A(1)" == stringWriter.toString)
  }

  test("apply A to 1 and 2") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(OperEx(TlaOper.apply, name("A"), int(1), int(2)))
    printWriter.flush()
    assert("A(1, 2)" == stringWriter.toString)
  }

  test("assignment: x' := 2") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(assignPrime(name("x"), int(2)))
    printWriter.flush()
    assert("x' := 2" == stringWriter.toString)
  }

  test("ENABLED and prime") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(enabled(prime(name("x"))))
    printWriter.flush()
    assert("ENABLED x'" == stringWriter.toString)
  }

  test("UNCHANGED") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(unchanged(name("x")))
    printWriter.flush()
    assert("UNCHANGED x" == stringWriter.toString)
  }

  test("[A]_vars") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(stutt(name("A"), name("vars")))
    printWriter.flush()
    assert("[A]_vars" == stringWriter.toString)
  }

  test("<A>_vars") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(nostutt(name("A"), name("vars")))
    printWriter.flush()
    assert("<A>_vars" == stringWriter.toString)
  }

  test("A \\cdot B") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(comp(name("A"), name("B")))
    printWriter.flush()
    assert("A \\cdot B" == stringWriter.toString)
  }

  test("WF_vars(A)") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(WF(name("vars"), name("A")))
    printWriter.flush()
    assert("WF_vars(A)" == stringWriter.toString)
  }

  test("SF_vars(A)") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(SF(name("vars"), name("A")))
    printWriter.flush()
    assert("SF_vars(A)" == stringWriter.toString)
  }

  test("[]A") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(box(name("A")))
    printWriter.flush()
    assert("[]A" == stringWriter.toString)
  }

  test("<>A") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(diamond(name("A")))
    printWriter.flush()
    assert("<>A" == stringWriter.toString)
  }

  test("A ~> B") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(leadsTo(name("A"), name("B")))
    printWriter.flush()
    assert("A ~> B" == stringWriter.toString)
  }

  test("A -+-> B") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(guarantees(name("A"), name("B")))
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
    writer.write(enumSet(int(42)))
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
      """{ 1,
        |  2,
        |  3,
        |  4,
        |  5,
        |  6,
        |  7,
        |  8,
        |  9,
        |  10 }""".stripMargin
    // Igor: I would prefer the layout below, but do not know how to do it with kiama
    val iLikeItBetterButItDoesNotWork =
      """{
        |  1,
        |  2,
        |  3,
        |  4,
        |  5,
        |  6,
        |  7,
        |  8,
        |  9,
        |  10
        |}""".stripMargin
    val result = stringWriter.toString
    assert(expected == result)
  }

  test("one-line tuple") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(tuple(int(1), int(2), int(3)))
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
    writer.write(times(name("X"), name("Y"), name("Z")))
    printWriter.flush()
    assert("X \\X Y \\X Z" == stringWriter.toString)
  }

  test("multi-line Cartesian product") {
    val writer = new PrettyWriter(printWriter, 40)
    writer.write(times(name("verylongname1"), name("verylongname2"), name("verylongname3")))
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
    val expr = impl(bool(true), and(1.to(5) map (_ => name("verylongname")): _*))
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

  test("~x") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(not(name("x")))
    printWriter.flush()
    assert("~x" == stringWriter.toString)
  }

  test("~(1 = 2)") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(not(eql(int(1), int(2))))
    printWriter.flush()
    assert("~(1 = 2)" == stringWriter.toString)
  }

  test("[S -> T]") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(funSet(name("S"), name("T")))
    printWriter.flush()
    assert("[S -> T]" == stringWriter.toString)
  }

  test("L2 :: 1") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(label(int(1), "L2"))
    printWriter.flush()
    assert("L2 :: 1" == stringWriter.toString)
  }

  test("L2(a, b) :: 1") {
    val writer = new PrettyWriter(printWriter, 80)
    writer.write(label(int(1), "L2", "a", "b"))
    printWriter.flush()
    assert("L2(a, b) :: 1" == stringWriter.toString)
  }

  test("one-line exists") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = exists(name("x"), name("y"), name("z"))
    writer.write(expr)
    printWriter.flush()
    // a multi-line vertical box always breaks from the previous line, as otherwise it is incredibly hard to indent
    val expected = "\\E x \\in y: z"
    assert(expected == stringWriter.toString)
  }

  test("multi-line exists") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr =
      exists(name("verylongname1"), name("verylongname2"), name("verylongname3"))
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
      exists(name("verylongname1"), name("verylongname2"), name("verylongname3"))
    val ex2 =
      forall(name("verylong4"), name("verylong5"), ex1)
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
      EE(name("verylongname1"), name("verylongname2"))
    val ex2 =
      AA(name("verylong3"), ex1)
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
        str("x1"),
        name("x2"),
        str("x3"),
        name("x4"),
        str("x5"),
        name("x6")
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
        str("verylong1"),
        name("verylong2"),
        str("verylong3"),
        name("verylong4"),
        str("verylong5"),
        name("verylong6")
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
        str("verylong1"),
        name("verylong2"),
        str("verylong3"),
        name("verylong4"),
        str("verylong5"),
        name("verylong6")
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

  test("TLC @@") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = atat(str("a"), int(1), str("b"), int(2), str("c"), int(3))
    writer.write(expr)
    printWriter.flush()
    val expected = """"a" :> 1 @@ "b" :> 2 @@ "c" :> 3""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line set of records") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = recSet(
        str("x1"),
        name("x2"),
        str("x3"),
        name("x4"),
        str("x5"),
        name("x6")
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
        str("verylong1"),
        name("verylong2"),
        str("verylong3"),
        name("verylong4"),
        str("verylong5"),
        name("verylong6")
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
    val expr = funDef(plus(name("x"), name("y")), name("x"), name("S"), name("y"), name("T"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """[ x \in S, y \in T |-> x + y ]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line function") {
    val writer = new PrettyWriter(printWriter, 30)
    val expr = funDef(plus(name("verylong1"), name("verylong2")), name("verylong1"), name("verylong3"),
        name("verylong2"), name("verylong4"))
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
    val expr = map(plus(name("x"), name("y")), name("x"), name("S"), name("y"), name("T"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{ x + y: x \in S, y \in T }""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line map") {
    val writer = new PrettyWriter(printWriter, 30)
    val expr = map(plus(name("verylong1"), name("verylong2")), name("verylong1"), name("verylong3"), name("verylong2"),
        name("verylong4"))
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
    val expr = filter(name("x"), name("S"), name("P"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{ x \in S: P }""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("precedence in filter") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = filter(name("x"), name("S"), lt(name("x"), int(5)))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """{ x \in S: x < 5 }""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line filter") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = filter(name("verylongname1"), name("verylongname2"), name("verylongname3"))

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
    val expr = appFun(name("f"), name("e"))
    writer.write(expr)
    printWriter.flush()
    val expected = """f[e]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line function application") {
    val writer = new PrettyWriter(printWriter, 20)
    val expr = appFun(name("verylongname1"), name("verylongname2"))
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
    val expr = ite(name("a"), name("b"), name("c"))
    writer.write(expr)
    printWriter.flush()
    val expected = """IF a THEN b ELSE c""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line IF-THEN-ELSE") {
    val writer = new PrettyWriter(printWriter, 20)
    val expr = ite(name("verylongname1"), name("verylongname2"), name("verylongname3"))
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
    val expr = except(name("f"), name("k"), name("v"))
    writer.write(expr)
    printWriter.flush()
    val expected = """[ f EXCEPT ![k] = v ]""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line EXCEPT") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = except(
        name("verylongname1"),
        name("verylongname2"),
        name("verylongname3")
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
        name("verylongname1"),
        name("verylongname2"),
        name("verylongname3"),
        name("verylongname4"),
        name("verylongname5")
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
    val expr = card(name("S"))
    writer.write(expr)
    printWriter.flush()
    val expected = """Cardinality(S)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("<<a>> \\o <<b>>") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = concat(tuple(name("a")), tuple(name("b")))
    writer.write(expr)
    printWriter.flush()
    val expected = """<<a>> \o <<b>>""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("Append(<<a>>, b)") {
    val writer = new PrettyWriter(printWriter, 80)
    val expr = append(tuple(name("a")), name("b"))
    writer.write(expr)
    printWriter.flush()
    val expected = """Append(<<a>>, b)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line CASE") {
    val writer = new PrettyWriter(printWriter, 40)
    val expr = caseSplit(name("guard1"), name("action1"), name("guard2"), name("action2"))
    writer.write(expr)
    printWriter.flush()
    val expected =
      """CASE guard1 -> action1
        |  [] guard2 -> action2""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a concise multi-line CASE") {
    val writer = new PrettyWriter(printWriter, 15)
    val expr = caseSplit(name("guard1"), name("action1"), name("guard2"), name("action2"))
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
    val expr = caseOther(name("otherAction"), name("guard1"), name("action1"), name("guard2"), name("action2"))
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
    val aDecl = TlaOperDecl("A", List(), int(1))
    val expr = letIn(appDecl(aDecl), aDecl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LET A == 1 IN A""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a multi-line LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val decl =
      TlaOperDecl("AVeryLongName", List(SimpleFormalParam("param1"), SimpleFormalParam("param2")),
          plus(name("param1"), name("param2")))
    val expr = letIn(appDecl(decl, int(1), int(2)), decl)
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
      TlaOperDecl("AVeryLongName", List(SimpleFormalParam("param1"), SimpleFormalParam("param2")),
          plus(name("param1"), name("param2")))
    val decl2 =
      TlaOperDecl("BVeryLongName", List(SimpleFormalParam("param1"), SimpleFormalParam("param2")),
          plus(name("param1"), name("param2")))
    val expr = letIn(mult(appDecl(decl1, int(1), int(2)), appDecl(decl2, int(3), int(4))), decl1, decl2)
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

  test("a LAMBDA as LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val aDecl = TlaOperDecl("LAMBDA", List(SimpleFormalParam("x")), NameEx("x"))
    val expr = letIn(NameEx("LAMBDA"), aDecl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LAMBDA x: x""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("nested lambdas") {
    // A(LAMBDA x: A(LAMBDA y: y, x), z)
    val writer = new PrettyWriter(printWriter, 40)
    // A(LAMBDA y: y + 1, x)
    val innerDecl =
      TlaOperDecl("LAMBDA", List(SimpleFormalParam("y")), tla.name("y"))
    val innerLambda = tla.letIn(tla.name("LAMBDA"), innerDecl)
    val innerA = tla.appOp(tla.name("A"), innerLambda, tla.name("x"))
    // A(LAMBDA x: A(LAMBDA y: y + 1, x), z)
    val outerDecl =
      TlaOperDecl("LAMBDA", List(SimpleFormalParam("x")), innerA)
    val outerLambda = letIn(NameEx("LAMBDA"), outerDecl)
    val outerA = tla.appOp(tla.name("A"), outerLambda, tla.name("z"))
    writer.write(outerA)
    printWriter.flush()
    val expected =
      """A(LAMBDA x: A(LAMBDA y: y, x), z)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line operator declaration") {
    val writer = new PrettyWriter(printWriter, 40)
    val body =
      OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), NameEx("x"))

    val fDecl = TlaOperDecl(
        "A",
        List(SimpleFormalParam("x")),
        body
    ) ///
    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """A(x) == 1 + x
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a recursive operator declaration") {
    val writer = new PrettyWriter(printWriter, 40)
    val body =
      OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), OperEx(TlaOper.apply, NameEx("A"), NameEx("x")))

    val fDecl = TlaOperDecl(
        "A",
        List(SimpleFormalParam("x")),
        body
    ) ///
    fDecl.isRecursive = true

    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """RECURSIVE A(_)
        |A(x) == 1 + A(x)
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a recursive operator declaration in LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val body =
      OperEx(TlaArithOper.plus, ValEx(TlaInt(1)), OperEx(TlaOper.apply, NameEx("A"), NameEx("x")))

    val fDecl = TlaOperDecl(
        "A",
        List(SimpleFormalParam("x")),
        body
    ) ///
    fDecl.isRecursive = true

    val letInEx = letIn(OperEx(TlaOper.apply, NameEx("A"), ValEx(TlaInt(1))), fDecl)

    writer.write(letInEx)
    printWriter.flush()
    // Igor: I would prefer to have an actual line-break between the recursive signature and the operator definition.
    // However, it is not clear to me how to enforce that in the pretty printer that we are using.
    val expected =
      """LET RECURSIVE A(_) A(x) == 1 + A(x) IN
        |A(1)""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line recursive function in LET-IN") {
    val writer = new PrettyWriter(printWriter, 40)
    val recFun =
      OperEx(TlaFunOper.recFunDef,
          OperEx(TlaArithOper.plus, ValEx(TlaInt(1)),
              OperEx(TlaFunOper.app, OperEx(TlaFunOper.recFunRef), NameEx("x"))), NameEx("x"), NameEx("S"))
    val fDecl = TlaOperDecl(
        "f",
        List(),
        recFun
    ) ///
    val expr = letIn(appDecl(fDecl), fDecl)
    writer.write(expr)
    printWriter.flush()
    val expected =
      """LET f[x \in S] == 1 + f[x] IN f""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("a one-line recursive function declaration") {
    val writer = new PrettyWriter(printWriter, 40)
    val recFun =
      OperEx(TlaFunOper.recFunDef,
          OperEx(TlaArithOper.plus, ValEx(TlaInt(1)),
              OperEx(TlaFunOper.app, OperEx(TlaFunOper.recFunRef), NameEx("x"))), NameEx("x"), NameEx("S"))
    val fDecl = TlaOperDecl(
        "f",
        List(),
        recFun
    ) ///
    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """f[x \in S] == 1 + f[x]
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

  test("declaration of a recursive function of two arguments") {
    val writer = new PrettyWriter(printWriter, 40)
    val body = tla.appFun(tla.recFunRef(), tla.tuple(tla.name("y"), tla.name("x")))
    val recFun =
      tla.recFunDef(body, tla.name("x"), tla.name("S"), tla.name("y"), tla.name("S"))

    val fDecl = TlaOperDecl("f", List(), recFun)
    writer.write(fDecl)
    printWriter.flush()
    val expected =
      """f[x \in S, y \in S] == f[y, x]
        |
        |""".stripMargin
    assert(expected == stringWriter.toString)
  }

}
