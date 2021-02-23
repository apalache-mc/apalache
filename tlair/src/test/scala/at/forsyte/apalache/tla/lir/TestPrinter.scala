package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.io.{Printer, SimplePrinter, UTFPrinter}
import at.forsyte.apalache.tla.lir.values.TlaInt
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner
import at.forsyte.apalache.tla.lir.UntypedPredefs.untyped

@RunWith(classOf[JUnitRunner])
class TestPrinter extends FunSuite with TestingPredefs {
  val bd = Builder

  val up = UTFPrinter
  val sp = SimplePrinter

  val ALSO_PRINT = false

  object rmp extends Printer {
    def apply(p_ex: TlaEx): String = UTFPrinter.apply(p_ex, true)
  }

  implicit def str(p_ex: TlaEx): String = up(p_ex)

  test("Test UTF8: TlaOper") {

    val eqEx1: String = bd.eql(n_a, n_b)
    val eqEx2: String = bd.eql(bd.plus(n_a, n_b), bd.minus(n_c, n_d))

    if (ALSO_PRINT) printlns(eqEx1, eqEx2)

    assert(eqEx1 == "a = b")
    assert(eqEx2 == "(a + b) = (c - d)")

    val neEx1: String = bd.neql(n_a, n_b)
    val neEx2: String = bd.neql(bd.plus(n_a, n_b), bd.minus(n_c, n_d))

    if (ALSO_PRINT) {
      printsep()
      printlns(neEx1, neEx2)
    }

    assert(neEx1 == "a %s b".format(up.m_neq))
    assert(neEx2 == "(a + b) %s (c - d)".format(up.m_neq))

    val appEx1: String = bd.appOp(n_x)
    val appEx2: String = bd.appOp(n_x, n_a)
    val appEx3: String = bd.appOp(n_x, seq(3): _*)
    val appEx4: String = bd.appOp(n_a, bd.appOp(n_b))
    val appEx5: String = bd.appOp(n_a, bd.appOp(n_b, n_c), bd.appOp(n_d, n_e))

    if (ALSO_PRINT) {
      printsep()
      printlns(appEx1, appEx2, appEx3, appEx4, appEx5)(true)
    }

    assert(appEx1 == "x()")
    assert(appEx2 == "x(a)")
    assert(appEx3 == "x(a, b, c)")
    assert(appEx4 == "a(b())")
    assert(appEx5 == "a(b(c), d(e))")

    val chooseEx1: String = bd.choose(n_x, n_p)
    val chooseEx2: String = bd.choose(n_x, n_S, n_p)
    val chooseEx3: String = bd.choose(n_x, bd.and(n_p, n_q))
    val chooseEx4: String = bd.choose(n_x, bd.times(n_S, n_T), bd.and(n_p, n_q))

    if (ALSO_PRINT) {
      printsep()
      printlns(chooseEx1, chooseEx2, chooseEx3, chooseEx4)
    }

    assert(chooseEx1 == "CHOOSE x : p")
    assert(chooseEx2 == "CHOOSE x %s S : p".format(up.m_in))
    assert(chooseEx3 == "CHOOSE x : (p %s q)".format(up.m_and))
    assert(chooseEx4 == "CHOOSE x %s (S %s T) : (p %s q)".format(up.m_in, up.m_times, up.m_and))

  }

  test("Test UTF8: TlaBoolOper") {

    val andEx1: String = bd.and()
    val andEx2: String = bd.and(n_a)
    val andEx3: String = bd.and(n_a, n_b)
    val andEx4: String = bd.and(n_a, bd.and(n_b, n_c))
    val andEx5: String = bd.and(n_a, bd.appOp(n_b))

    if (ALSO_PRINT) {
      printsep()
      printlns(andEx1, andEx2, andEx3, andEx4, andEx5)
    }

    assert(andEx1 == "")
    assert(andEx2 == "a")
    assert(andEx3 == "a %s b".format(up.m_and))
    assert(andEx4 == "a %s (b %s c)".format(up.m_and, up.m_and))
    assert(andEx5 == "a %s b()".format(up.m_and))

    val orEx1: String = bd.or()
    val orEx2: String = bd.or(n_a)
    val orEx3: String = bd.or(n_a, n_b)
    val orEx4: String = bd.or(n_a, bd.or(n_b, n_c))
    val orEx5: String = bd.or(n_a, bd.appOp(n_b))

    if (ALSO_PRINT) {
      printsep()
      printlns(orEx1, orEx2, orEx3, orEx4, orEx5)
    }

    assert(orEx1 == "")
    assert(orEx2 == "a")
    assert(orEx3 == "a %s b".format(up.m_or))
    assert(orEx4 == "a %s (b %s c)".format(up.m_or, up.m_or))
    assert(orEx5 == "a %s b()".format(up.m_or))

    val notEx1: String = bd.not(n_a)
    val notEx2: String = bd.not(bd.and(n_a, n_b))

    if (ALSO_PRINT) {
      printsep()
      printlns(notEx1, notEx2)
    }

    assert(notEx1 == "%sa".format(up.m_not))
    assert(notEx2 == "%s(a %s b)".format(up.m_not, up.m_and))

    val implEx1: String = bd.impl(n_p, n_q)
    val implEx2: String = bd.impl(bd.and(n_p, n_q), bd.or(n_a, n_b))
    val implEx3: String = bd.impl(bd.and(n_p), bd.and(n_q))

    if (ALSO_PRINT) {
      printsep()
      printlns(implEx1, implEx2, implEx3)
    }

    assert(implEx1 == "p %s q".format(up.m_impl))
    assert(implEx2 == "(p %s q) %s (a %s b)".format(up.m_and, up.m_impl, up.m_or))
    assert(implEx3 == "p %s q".format(up.m_impl))

    val equivEx1: String = bd.equiv(n_p, n_q)
    val equivEx2: String = bd.equiv(bd.and(n_p, n_q), bd.or(n_a, n_b))
    val equivEx3: String = bd.equiv(bd.and(n_p), bd.and(n_q))

    if (ALSO_PRINT) {
      printsep()
      printlns(equivEx1, equivEx2, equivEx3)
    }

    assert(equivEx1 == "p %s q".format(up.m_equiv))
    assert(equivEx2 == "(p %s q) %s (a %s b)".format(up.m_and, up.m_equiv, up.m_or))
    assert(equivEx3 == "p %s q".format(up.m_equiv))

    val forallEx1: String = bd.forall(n_a, n_b)
    val forallEx2: String = bd.forall(n_a, bd.or(seq(2, 1): _*))
    val forallEx3: String = bd.forall(n_a, n_b, n_c)
    val forallEx4: String = bd.forall(n_a, bd.times(seq(2, 1): _*), bd.and(seq(2, 3): _*))

    if (ALSO_PRINT) {
      printsep()
      printlns(forallEx1, forallEx2, forallEx3, forallEx4)
    }

    assert(forallEx1 == "%sa: b".format(up.m_forall))
    assert(forallEx2 == "%sa: (b %s c)".format(up.m_forall, up.m_or))
    assert(forallEx3 == "%sa %s b: c".format(up.m_forall, up.m_in))
    assert(forallEx4 == "%sa %s (b %s c): (d %s e)".format(up.m_forall, up.m_in, up.m_times, up.m_and))

    val existsEx1: String = bd.exists(n_a, n_b)
    val existsEx2: String = bd.exists(n_a, bd.or(seq(2, 1): _*))
    val existsEx3: String = bd.exists(n_a, n_b, n_c)
    val existsEx4: String = bd.exists(n_a, bd.times(seq(2, 1): _*), bd.and(seq(2, 3): _*))

    if (ALSO_PRINT) {
      printsep()
      printlns(existsEx1, existsEx2, existsEx3, existsEx4)
    }

    assert(existsEx1 == "%sa: b".format(up.m_exists))
    assert(existsEx2 == "%sa: (b %s c)".format(up.m_exists, up.m_or))
    assert(existsEx3 == "%sa %s b: c".format(up.m_exists, up.m_in))
    assert(existsEx4 == "%sa %s (b %s c): (d %s e)".format(up.m_exists, up.m_in, up.m_times, up.m_and))

  }

  test("Test UTF8: TlaArithOper") {}

  test("Test UTF8: TlaSetOper") {
    val inEx1: String = bd.in(n_a, n_b)
    val inEx2: String = bd.and(bd.in(n_a, n_b), bd.in(n_c, n_d))

    if (ALSO_PRINT) {
      printsep()
      printlns(inEx1, inEx2)
    }
  }

  // regression
  test("Test UTF8: OperFormalParam") {
    val d = TlaOperDecl("Foo", List(OperFormalParam("Bar", 1)), ValEx(TlaInt(1)))
    assert("Foo(Bar(_)) ≜ 1" == UTFPrinter(d))
  }
}
