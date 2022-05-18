package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestBoolRule extends AnyFunSuite {
  val rewriter = ToTermRewriterImpl()

  val rule = new BoolRule(rewriter)

  val b = BoolT1

  val p = tla.name("p").as(b)
  val pVar = BoolVar("p")
  val q = tla.name("q").as(b)
  val qVar = BoolVar("q")

  val expected: Map[TlaEx, BoolExpr] = Map(
      (tla.and(p, q).as(b)) -> And(pVar, qVar),
      (tla.not(p).as(b)) -> Neg(pVar),
      (tla.or(tla.impl(p, q).as(b), p).as(b)) -> Or(Impl(pVar, qVar), pVar),
  )

  test("BoolRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
    }

    import at.forsyte.apalache.tla.lir.UntypedPredefs._

    val notApp = List(
        tla.tuple(tla.int(1), tla.int(2)),
        tla.funSet(tla.name("S"), tla.dotdot(tla.int(1), tla.int(42))),
        tla.unchanged(tla.name("x")),
        tla.forall(tla.name("x"), tla.name("S"), tla.name("p")),
        tla.int(2),
        tla.bool(true),
    )

    notApp.foreach { ex =>
      assert(!rule.isApplicable(ex.untyped()))
    }
  }

  test("BoolRule correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k)
      assert(actual == expected)
    }
  }

}
