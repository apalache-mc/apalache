package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, IntT1, SetT1, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestQuantRule extends AnyFunSuite {

  val sType = ConstT1("SSORT")
  val sSort = UninterpretedSort("SSORT")

  val constSets = Map("S" -> sSort)

  val rewriter = ToTermRewriterImpl(constSets)

  val rule = new QuantifierRule(rewriter, new RestrictedSetJudgement(constSets))

  val b = BoolT1

  val p = tla.name("p").as(b)
  val pVar = BoolVar("p")
  val q = tla.name("q").as(b)
  val qVar = BoolVar("q")

  val x = tla.name("x").as(sType)
  val y = tla.name("y").as(IntT1)
  val set = tla.name("S").as(SetT1(sType))
  val intSet = tla.intSet().as(SetT1(IntT1))

  val expected: Map[TlaEx, BoolExpr] = Map(
      (tla.exists(x, set, p).as(b)) -> Exists(List(("x", sSort)), pVar),
      (tla.forall(y, intSet, q).as(b)) -> Forall(List(("y", IntSort())), qVar),
  )

  test("QuantRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
    }

    assertThrows[RewriterException] {
      val tType = ConstT1("TSORT")
      rule(tla.exists(tla.name("t").as(tType), tla.name("T").as(tType), p).as(b))
    }

    import at.forsyte.apalache.tla.lir.UntypedPredefs._

    val notApp = List(
        tla.tuple(tla.int(1), tla.int(2)),
        tla.funSet(tla.name("S"), tla.dotdot(tla.int(1), tla.int(42))),
        tla.unchanged(tla.name("x")),
        tla.and(tla.name("x"), tla.name("T"), tla.name("p")),
        tla.int(2),
        tla.bool(true),
    )

    notApp.foreach { ex =>
      assert(!rule.isApplicable(ex.untyped()))
    }
  }

  test("QuantRule correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k)
      assert(actual == expected)
    }
  }
}
