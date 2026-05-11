package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.io.UTFPrinter
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
    val S = tla.name("S")
    val T = tla.name("T")
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val e = tla.name("e")
    val p = tla.name("p")
    val q = tla.name("q")
    val x = tla.name("x")

    val eqEx1: String = toUtf(tla.eql(a, b))
    val eqEx2: String = toUtf(tla.eql(tla.plus(a, b), tla.minus(c, d)))

    assert(eqEx1 == "a = b")
    assert(eqEx2 == "(a + b) = (c - d)")

    val neEx1: String = toUtf(tla.neql(a, b))
    val neEx2: String = toUtf(tla.neql(tla.plus(a, b), tla.minus(c, d)))

    assert(neEx1 == "a %s b".format(toUtf.m_neq))
    assert(neEx2 == "(a + b) %s (c - d)".format(toUtf.m_neq))

    val appEx1: String = toUtf(tla.appOp(x))
    val appEx2: String = toUtf(tla.appOp(x, a))
    val appEx3: String = toUtf(tla.appOp(x, a, b, c))
    val appEx4: String = toUtf(tla.appOp(a, tla.appOp(b)))
    val appEx5: String = toUtf(tla.appOp(a, tla.appOp(b, c), tla.appOp(d, e)))

    assert(appEx1 == "x()")
    assert(appEx2 == "x(a)")
    assert(appEx3 == "x(a, b, c)")
    assert(appEx4 == "a(b())")
    assert(appEx5 == "a(b(c), d(e))")

    val chooseEx1: String = toUtf(tla.choose(x, p))
    val chooseEx2: String = toUtf(tla.choose(x, S, p))
    val chooseEx3: String = toUtf(tla.choose(x, tla.and(p, q)))
    val chooseEx4: String = toUtf(tla.choose(x, tla.times(S, T), tla.and(p, q)))

    assert(chooseEx1 == "CHOOSE x : p")
    assert(chooseEx2 == "CHOOSE x %s S : p".format(toUtf.m_in))
    assert(chooseEx3 == "CHOOSE x : (p %s q)".format(toUtf.m_and))
    assert(chooseEx4 == "CHOOSE x %s (S %s T) : (p %s q)".format(toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaBoolOper") {
    val a = tla.name("a")
    val b = tla.name("b")
    val c = tla.name("c")
    val d = tla.name("d")
    val e = tla.name("e")
    val p = tla.name("p")
    val q = tla.name("q")

    val andEx1: String = toUtf(tla.and())
    val andEx2: String = toUtf(tla.and(a))
    val andEx3: String = toUtf(tla.and(a, b))
    val andEx4: String = toUtf(tla.and(a, tla.and(b, c)))
    val andEx5: String = toUtf(tla.and(a, tla.appOp(b)))

    assert(andEx1 == "")
    assert(andEx2 == "a")
    assert(andEx3 == "a %s b".format(toUtf.m_and))
    assert(andEx4 == "a %s (b %s c)".format(toUtf.m_and, toUtf.m_and))
    assert(andEx5 == "a %s b()".format(toUtf.m_and))

    val orEx1: String = toUtf(tla.or())
    val orEx2: String = toUtf(tla.or(a))
    val orEx3: String = toUtf(tla.or(a, b))
    val orEx4: String = toUtf(tla.or(a, tla.or(b, c)))
    val orEx5: String = toUtf(tla.or(a, tla.appOp(b)))

    assert(orEx1 == "")
    assert(orEx2 == "a")
    assert(orEx3 == "a %s b".format(toUtf.m_or))
    assert(orEx4 == "a %s (b %s c)".format(toUtf.m_or, toUtf.m_or))
    assert(orEx5 == "a %s b()".format(toUtf.m_or))

    val notEx1: String = toUtf(tla.not(a))
    val notEx2: String = toUtf(tla.not(tla.and(a, b)))

    assert(notEx1 == "%sa".format(toUtf.m_not))
    assert(notEx2 == "%s(a %s b)".format(toUtf.m_not, toUtf.m_and))

    val implEx1: String = toUtf(tla.impl(p, q))
    val implEx2: String = toUtf(tla.impl(tla.and(p, q), tla.or(a, b)))
    val implEx3: String = toUtf(tla.impl(tla.and(p), tla.and(q)))

    assert(implEx1 == "p %s q".format(toUtf.m_impl))
    assert(implEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_impl, toUtf.m_or))
    assert(implEx3 == "p %s q".format(toUtf.m_impl))

    val equivEx1: String = toUtf(tla.equiv(p, q))
    val equivEx2: String = toUtf(tla.equiv(tla.and(p, q), tla.or(a, b)))
    val equivEx3: String = toUtf(tla.equiv(tla.and(p), tla.and(q)))

    assert(equivEx1 == "p %s q".format(toUtf.m_equiv))
    assert(equivEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_equiv, toUtf.m_or))
    assert(equivEx3 == "p %s q".format(toUtf.m_equiv))

    val forallEx1: String = toUtf(tla.forall(a, b))
    val forallEx2: String = toUtf(tla.forall(a, tla.or(b, c)))
    val forallEx3: String = toUtf(tla.forall(a, b, c))
    val forallEx4: String =
      toUtf(tla.forall(a, tla.times(b, c), tla.and(d, e)))

    assert(forallEx1 == "%sa: b".format(toUtf.m_forall))
    assert(forallEx2 == "%sa: (b %s c)".format(toUtf.m_forall, toUtf.m_or))
    assert(forallEx3 == "%sa %s b: c".format(toUtf.m_forall, toUtf.m_in))
    assert(forallEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_forall, toUtf.m_in, toUtf.m_times, toUtf.m_and))

    val existsEx1: String = toUtf(tla.exists(a, b))
    val existsEx2: String = toUtf(tla.exists(a, tla.or(b, c)))
    val existsEx3: String = toUtf(tla.exists(a, b, c))
    val times = tla.times(b, c)
    val and = tla.and(d, e)
    val existsEx4: String = toUtf(tla.exists(a, times, and))

    assert(existsEx1 == "%sa: b".format(toUtf.m_exists))
    assert(existsEx2 == "%sa: (b %s c)".format(toUtf.m_exists, toUtf.m_or))
    assert(existsEx3 == "%sa %s b: c".format(toUtf.m_exists, toUtf.m_in))
    assert(existsEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_exists, toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaArithOper") {}

  test("Test UTF8: TlaSetOper") {}

  test("Test UTF8: TlaAssumeDecl") {
    val x = tla.name("x")
    val namedAssume: String = toUtf(TlaAssumeDecl(Some("myAssume"), tla.eql(x, tla.bool(true))))
    assert(namedAssume == s"ASSUME myAssume ≜ x = TRUE")

    val unnamedAssume: String = toUtf(TlaAssumeDecl(None, tla.eql(x, tla.bool(true))))
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
    val a = tla.name("a")
    val c = tla.name("c")
    val p = tla.name("p")
    val decl = TlaOperDecl("c", List(), ValEx(TlaInt(1)))
    val letInEx = tla.letIn(tla.appOp(c), decl)
    val caseEx = tla.caseOther(letInEx, p, a)
    assert(toUtf(caseEx).contains("OTHER → (LET c"))
  }
}
