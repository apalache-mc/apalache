package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.io.{Printer, SimplePrinter, UTFPrinter}
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.convenience._

import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs._

@RunWith(classOf[JUnitRunner])
class TestPrinter extends FunSuite with TestingPredefs {
  val toUtf = UTFPrinter
  val sp = SimplePrinter

  val ALSO_PRINT = false

  object rmp extends Printer {
    def apply(p_ex: TlaEx): String = UTFPrinter.apply(p_ex, true)
  }

  test("Test UTF8: TlaOper") {

    val eqEx1: String = toUtf(tla.eql(n_a, n_b))
    val eqEx2: String = toUtf(tla.eql(tla.plus(n_a, n_b), tla.minus(n_c, n_d)))

    if (ALSO_PRINT) printlns(eqEx1, eqEx2)

    assert(eqEx1 == "a = b")
    assert(eqEx2 == "(a + b) = (c - d)")

    val neEx1: String = toUtf(tla.neql(n_a, n_b))
    val neEx2: String = toUtf(tla.neql(tla.plus(n_a, n_b), tla.minus(n_c, n_d)))

    if (ALSO_PRINT) {
      printsep()
      printlns(neEx1, neEx2)
    }

    assert(neEx1 == "a %s b".format(toUtf.m_neq))
    assert(neEx2 == "(a + b) %s (c - d)".format(toUtf.m_neq))

    val appEx1: String = toUtf(tla.appOp(n_x))
    val appEx2: String = toUtf(tla.appOp(n_x, n_a))
    val appEx3: String = toUtf(tla.appOp(n_x, seq(3).map(tla.fromTlaEx): _*))
    val appEx4: String = toUtf(tla.appOp(n_a, tla.appOp(n_b)))
    val appEx5: String = toUtf(tla.appOp(n_a, tla.appOp(n_b, n_c), tla.appOp(n_d, n_e)))

    if (ALSO_PRINT) {
      printsep()
      printlns(appEx1, appEx2, appEx3, appEx4, appEx5)(true)
    }

    assert(appEx1 == "x()")
    assert(appEx2 == "x(a)")
    assert(appEx3 == "x(a, b, c)")
    assert(appEx4 == "a(b())")
    assert(appEx5 == "a(b(c), d(e))")

    val chooseEx1: String = toUtf(tla.choose(n_x, n_p))
    val chooseEx2: String = toUtf(tla.choose(n_x, n_S, n_p))
    val chooseEx3: String = toUtf(tla.choose(n_x, tla.and(n_p, n_q)))
    val chooseEx4: String = toUtf(tla.choose(n_x, tla.times(n_S, n_T), tla.and(n_p, n_q)))

    if (ALSO_PRINT) {
      printsep()
      printlns(chooseEx1, chooseEx2, chooseEx3, chooseEx4)
    }

    assert(chooseEx1 == "CHOOSE x : p")
    assert(chooseEx2 == "CHOOSE x %s S : p".format(toUtf.m_in))
    assert(chooseEx3 == "CHOOSE x : (p %s q)".format(toUtf.m_and))
    assert(chooseEx4 == "CHOOSE x %s (S %s T) : (p %s q)".format(toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaBoolOper") {

    val andEx1: String = toUtf(tla.and())
    val andEx2: String = toUtf(tla.and(n_a))
    val andEx3: String = toUtf(tla.and(n_a, n_b))
    val andEx4: String = toUtf(tla.and(n_a, tla.and(n_b, n_c)))
    val andEx5: String = toUtf(tla.and(n_a, tla.appOp(n_b)))

    if (ALSO_PRINT) {
      printsep()
      printlns(andEx1, andEx2, andEx3, andEx4, andEx5)
    }

    assert(andEx1 == "")
    assert(andEx2 == "a")
    assert(andEx3 == "a %s b".format(toUtf.m_and))
    assert(andEx4 == "a %s (b %s c)".format(toUtf.m_and, toUtf.m_and))
    assert(andEx5 == "a %s b()".format(toUtf.m_and))

    val orEx1: String = toUtf(tla.or())
    val orEx2: String = toUtf(tla.or(n_a))
    val orEx3: String = toUtf(tla.or(n_a, n_b))
    val orEx4: String = toUtf(tla.or(n_a, tla.or(n_b, n_c)))
    val orEx5: String = toUtf(tla.or(n_a, tla.appOp(n_b)))

    if (ALSO_PRINT) {
      printsep()
      printlns(orEx1, orEx2, orEx3, orEx4, orEx5)
    }

    assert(orEx1 == "")
    assert(orEx2 == "a")
    assert(orEx3 == "a %s b".format(toUtf.m_or))
    assert(orEx4 == "a %s (b %s c)".format(toUtf.m_or, toUtf.m_or))
    assert(orEx5 == "a %s b()".format(toUtf.m_or))

    val notEx1: String = toUtf(tla.not(n_a))
    val notEx2: String = toUtf(tla.not(tla.and(n_a, n_b)))

    if (ALSO_PRINT) {
      printsep()
      printlns(notEx1, notEx2)
    }

    assert(notEx1 == "%sa".format(toUtf.m_not))
    assert(notEx2 == "%s(a %s b)".format(toUtf.m_not, toUtf.m_and))

    val implEx1: String = toUtf(tla.impl(n_p, n_q))
    val implEx2: String = toUtf(tla.impl(tla.and(n_p, n_q), tla.or(n_a, n_b)))
    val implEx3: String = toUtf(tla.impl(tla.and(n_p), tla.and(n_q)))

    if (ALSO_PRINT) {
      printsep()
      printlns(implEx1, implEx2, implEx3)
    }

    assert(implEx1 == "p %s q".format(toUtf.m_impl))
    assert(implEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_impl, toUtf.m_or))
    assert(implEx3 == "p %s q".format(toUtf.m_impl))

    val equivEx1: String = toUtf(tla.equiv(n_p, n_q))
    val equivEx2: String = toUtf(tla.equiv(tla.and(n_p, n_q), tla.or(n_a, n_b)))
    val equivEx3: String = toUtf(tla.equiv(tla.and(n_p), tla.and(n_q)))

    if (ALSO_PRINT) {
      printsep()
      printlns(equivEx1, equivEx2, equivEx3)
    }

    assert(equivEx1 == "p %s q".format(toUtf.m_equiv))
    assert(equivEx2 == "(p %s q) %s (a %s b)".format(toUtf.m_and, toUtf.m_equiv, toUtf.m_or))
    assert(equivEx3 == "p %s q".format(toUtf.m_equiv))

    val forallEx1: String = toUtf(tla.forall(n_a, n_b))
    val forallEx2: String = toUtf(tla.forall(n_a, tla.or(seq(2, 1).map(tla.fromTlaEx): _*)))
    val forallEx3: String = toUtf(tla.forall(n_a, n_b, n_c))
    val forallEx4: String =
      toUtf(tla.forall(n_a, tla.times(seq(2, 1).map(tla.fromTlaEx): _*), tla.and(seq(2, 3).map(tla.fromTlaEx): _*)))

    if (ALSO_PRINT) {
      printsep()
      printlns(forallEx1, forallEx2, forallEx3, forallEx4)
    }

    assert(forallEx1 == "%sa: b".format(toUtf.m_forall))
    assert(forallEx2 == "%sa: (b %s c)".format(toUtf.m_forall, toUtf.m_or))
    assert(forallEx3 == "%sa %s b: c".format(toUtf.m_forall, toUtf.m_in))
    assert(forallEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_forall, toUtf.m_in, toUtf.m_times, toUtf.m_and))

    val existsEx1: String = toUtf(tla.exists(n_a, n_b))
    val existsEx2: String = toUtf(tla.exists(n_a, tla.or(seq(2, 1).map(tla.fromTlaEx): _*)))
    val existsEx3: String = toUtf(tla.exists(n_a, n_b, n_c))
    val times = tla.times(seq(2, 1).map(tla.fromTlaEx): _*)
    val and = tla.and(seq(2, 3).map(tla.fromTlaEx): _*)
    val existsEx4: String = toUtf(tla.exists(n_a, times, and))

    if (ALSO_PRINT) {
      printsep()
      printlns(existsEx1, existsEx2, existsEx3, existsEx4)
    }

    assert(existsEx1 == "%sa: b".format(toUtf.m_exists))
    assert(existsEx2 == "%sa: (b %s c)".format(toUtf.m_exists, toUtf.m_or))
    assert(existsEx3 == "%sa %s b: c".format(toUtf.m_exists, toUtf.m_in))
    assert(existsEx4 == "%sa %s (b %s c): (d %s e)".format(toUtf.m_exists, toUtf.m_in, toUtf.m_times, toUtf.m_and))

  }

  test("Test UTF8: TlaArithOper") {}

  test("Test UTF8: TlaSetOper") {
    val inEx1: String = toUtf(tla.in(n_a, n_b))
    val inEx2: String = toUtf(tla.and(tla.in(n_a, n_b), tla.in(n_c, n_d)))

    if (ALSO_PRINT) {
      printsep()
      printlns(inEx1, inEx2)
    }
  }

  // regression
  test("Test UTF8: OperFormalParam") {
    val d = TlaOperDecl("Foo", List(OperParam("Bar", 1)), ValEx(TlaInt(1)))
    assert("Foo(Bar(_)) ≜ 1" == UTFPrinter(d))
  }
}
