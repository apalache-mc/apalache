package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.io.{UTFPrinter}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.convenience._

import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestPrinter extends AnyFunSuite {
  val toUtf = UTFPrinter

  test("Test UTF8: TlaOper") {

    val eqEx1: String = toUtf(tla.eql(tla.name("a"), tla.name("b")))
    val eqEx2: String = toUtf(tla.eql(tla.plus(tla.name("a"), tla.name("b")), tla.minus(tla.name("c"), tla.name("d"))))


    assert(eqEx1 == "a = b")
    assert(eqEx2 == "(a + b) = (c - d)")

    val neEx1: String = toUtf(tla.neql(tla.name("a"), tla.name("b")))
    val neEx2: String = toUtf(tla.neql(tla.plus(tla.name("a"), tla.name("b")), tla.minus(tla.name("c"), tla.name("d"))))


    assert(neEx1 == "a %s b".format(toUtf.m_neq))
    assert(neEx2 == "(a + b) %s (c - d)".format(toUtf.m_neq))

    val appEx1: String = toUtf(tla.appOp(tla.name("x")))
    val appEx2: String = toUtf(tla.appOp(tla.name("x"), tla.name("a")))
    val appEx3: String = toUtf(tla.appOp(tla.name("x"), tla.name("a"), tla.name("b"), tla.name("c")))
    val appEx4: String = toUtf(tla.appOp(tla.name("a"), tla.appOp(tla.name("b"))))
    val appEx5: String = toUtf(tla.appOp(tla.name("a"), tla.appOp(tla.name("b"), tla.name("c")), tla.appOp(tla.name("d"), tla.name("e"))))


    assert(appEx1 == "x()")
    assert(appEx2 == "x(a)")
    assert(appEx3 == "x(a, b, c)")
    assert(appEx4 == "a(b())")
    assert(appEx5 == "a(b(c), d(e))")

    val chooseEx1: String = toUtf(tla.choose(tla.name("x"), tla.name("p")))
    val chooseEx2: String = toUtf(tla.choose(tla.name("x"), tla.name("S"), tla.name("p")))
    val chooseEx3: String = toUtf(tla.choose(tla.name("x"), tla.and(tla.name("p"), tla.name("q"))))
    val chooseEx4: String = toUtf(tla.choose(tla.name("x"), tla.times(tla.name("S"), tla.name("T")), tla.and(tla.name("p"), tla.name("q"))))


    assert(chooseEx1 == "CHOOSE x : p")
    assert(chooseEx2 == "CHOOSE x %s S : p".format(toUtf.m_in))
    assert(chooseEx3 == "CHOOSE x : (p %s q)".format(toUtf.m_and))
    assert(chooseEx4 == "CHOOSE x %s (S %s T) : (p %s q)".format(toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaBoolOper") {

    val andEx1: String = toUtf(tla.and())
    val andEx2: String = toUtf(tla.and(tla.name("a")))
    val andEx3: String = toUtf(tla.and(tla.name("a"), tla.name("b")))
    val andEx4: String = toUtf(tla.and(tla.name("a"), tla.and(tla.name("b"), tla.name("c"))))
    val andEx5: String = toUtf(tla.and(tla.name("a"), tla.appOp(tla.name("b"))))


    assert(andEx1 == "")
    assert(andEx2 == "a")
    assert(andEx3 == "a %s b".format(toUtf.m_and))
    assert(andEx4 == "a %s (b %s c)".format(toUtf.m_and, toUtf.m_and))
    assert(andEx5 == "a %s b()".format(toUtf.m_and))

    val orEx1: String = toUtf(tla.or())
    val orEx2: String = toUtf(tla.or(tla.name("a")))
    val orEx3: String = toUtf(tla.or(tla.name("a"), tla.name("b")))
    val orEx4: String = toUtf(tla.or(tla.name("a"), tla.or(tla.name("b"), tla.name("c"))))
    val orEx5: String = toUtf(tla.or(tla.name("a"), tla.appOp(tla.name("b"))))


    assert(orEx1 == "")
    assert(orEx2 == "a")
    assert(orEx3 == "a %s b".format(toUtf.m_or))
    assert(orEx4 == "a %s (b %s c)".format(toUtf.m_or, toUtf.m_or))
    assert(orEx5 == "a %s b()".format(toUtf.m_or))

    val notEx1: String = toUtf(tla.not(tla.name("a")))
    val notEx2: String = toUtf(tla.not(tla.and(tla.name("a"), tla.name("b"))))


    assert(notEx1 == "%sa".format(toUtf.m_not))
    assert(notEx2 == "%s(a %s b)".format(toUtf.m_not, toUtf.m_and))

    val implEx1: String = toUtf(tla.impl(tla.name("p"), tla.name("q")))
    val implEx2: String = toUtf(tla.impl(tla.and(tla.name("p"), tla.name("q")), tla.or(tla.name("a"), tla.name("b"))))
    val implEx3: String = toUtf(tla.impl(tla.and(tla.name("p")), tla.and(tla.name("q"))))


    assert(implEx1 == "p %s q".format(toUtf.m_impl))
    assert(implEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_impl, toUtf.m_or))
    assert(implEx3 == "p %s q".format(toUtf.m_impl))

    val equivEx1: String = toUtf(tla.equiv(tla.name("p"), tla.name("q")))
    val equivEx2: String = toUtf(tla.equiv(tla.and(tla.name("p"), tla.name("q")), tla.or(tla.name("a"), tla.name("b"))))
    val equivEx3: String = toUtf(tla.equiv(tla.and(tla.name("p")), tla.and(tla.name("q"))))


    assert(equivEx1 == "p %s q".format(toUtf.m_equiv))
    assert(equivEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_equiv, toUtf.m_or))
    assert(equivEx3 == "p %s q".format(toUtf.m_equiv))

    val forallEx1: String = toUtf(tla.forall(tla.name("a"), tla.name("b")))
    val forallEx2: String = toUtf(tla.forall(tla.name("a"), tla.or(tla.name("b"), tla.name("c"))))
    val forallEx3: String = toUtf(tla.forall(tla.name("a"), tla.name("b"), tla.name("c")))
    val forallEx4: String =
      toUtf(tla.forall(tla.name("a"), tla.times(tla.name("b"), tla.name("c")), tla.and(tla.name("d"), tla.name("e"))))


    assert(forallEx1 == "%sa: b".format(toUtf.m_forall))
    assert(forallEx2 == "%sa: (b %s c)".format(toUtf.m_forall, toUtf.m_or))
    assert(forallEx3 == "%sa %s b: c".format(toUtf.m_forall, toUtf.m_in))
    assert(forallEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_forall, toUtf.m_in, toUtf.m_times, toUtf.m_and))

    val existsEx1: String = toUtf(tla.exists(tla.name("a"), tla.name("b")))
    val existsEx2: String = toUtf(tla.exists(tla.name("a"), tla.or(tla.name("b"), tla.name("c"))))
    val existsEx3: String = toUtf(tla.exists(tla.name("a"), tla.name("b"), tla.name("c")))
    val times = tla.times(tla.name("b"), tla.name("c"))
    val and = tla.and(tla.name("d"), tla.name("e"))
    val existsEx4: String = toUtf(tla.exists(tla.name("a"), times, and))


    assert(existsEx1 == "%sa: b".format(toUtf.m_exists))
    assert(existsEx2 == "%sa: (b %s c)".format(toUtf.m_exists, toUtf.m_or))
    assert(existsEx3 == "%sa %s b: c".format(toUtf.m_exists, toUtf.m_in))
    assert(existsEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_exists, toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaArithOper") {}

  test("Test UTF8: TlaSetOper") {}

  test("Test UTF8: TlaAssumeDecl") {
    val namedAssume: String = toUtf(TlaAssumeDecl(Some("myAssume"), tla.eql(tla.name("x"), tla.bool(true))))
    assert(namedAssume == s"ASSUME myAssume ≜ x = TRUE")

    val unnamedAssume: String = toUtf(TlaAssumeDecl(None, tla.eql(tla.name("x"), tla.bool(true))))
    assert(unnamedAssume == s"ASSUME x = TRUE")
  }

  // regression
  test("Test UTF8: OperFormalParam") {
    val d = TlaOperDecl("Foo", List(OperParam("Bar", 1)), ValEx(TlaInt(1)))
    assert("Foo(Bar(_)) ≜ 1" == UTFPrinter(d))
  }

  // regression: LET-IN in the OTHER branch of CASE must be parenthesized.
  // Without parens, `CASE p -> a [] OTHER -> LET c == 1 IN c` re-parses any
  // following `/\ b` as inside the LET scope rather than outside the CASE.
  test("LET-IN in CASE OTHER branch is parenthesized") {
    val decl = TlaOperDecl("c", List(), ValEx(TlaInt(1)))
    val letInEx = tla.letIn(tla.appOp(tla.name("c")), decl)
    val caseEx = tla.caseOther(letInEx, tla.name("p"), tla.name("a"))
    assert(toUtf(caseEx).contains("OTHER → (LET c"))
  }
}
