package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.formulas.Booleans.{BoolVar, True}
import at.forsyte.apalache.tla.lir.formulas.EUF.{UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.{IntLiteral, IntVar}
import at.forsyte.apalache.tla.lir.formulas.{Term, UninterpretedSort}
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, IntT1, StrT1, TlaEx}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestValueRule extends AnyFunSuite {

  val rule = new ValueRule

  val b = BoolT1
  val i = IntT1
  val aType = ConstT1("A")
  val bType = ConstT1("B")

  val intEx1 = tla.int(1).as(i)
  val intEx2 = tla.name("x").as(i)
  val intEx3 = tla.plus(intEx1, intEx2).as(i)

  val boolEx1 = tla.bool(true).as(b)
  val boolEx2 = tla.name("p").as(b)
  val boolEx3 = tla.and(boolEx1, boolEx2).as(b)

  val uninterpEx1 = tla.str("1_OF_A").as(aType)
  val uninterpEx2 = tla.name("v").as(bType)
  val uninterpEx3 = tla.str("string").as(StrT1)

  val expected: Map[TlaEx, Term] = Map(
      intEx1 -> IntLiteral(1),
      intEx2 -> IntVar("x"),
      boolEx1 -> True,
      boolEx2 -> BoolVar("p"),
      uninterpEx1 -> UninterpretedLiteral("1", UninterpretedSort("A")),
      uninterpEx2 -> UninterpretedVar("v", UninterpretedSort("B")),
      uninterpEx3 -> UninterpretedLiteral("string", UninterpretedSort(StrT1.toString)),
  )

  test("ValueRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
    }

    import at.forsyte.apalache.tla.lir.UntypedPredefs._

    val notApp = List(
        tla.and(tla.bool(true), tla.bool(false)),
        tla.impl(tla.name("x"), tla.name("q")),
        tla.tuple(tla.int(1), tla.int(2)),
        tla.funSet(tla.name("S"), tla.dotdot(tla.int(1), tla.int(42))),
        tla.unchanged(tla.name("x")),
        tla.forall(tla.name("x"), tla.name("S"), tla.name("p")),
    )

    notApp.foreach { ex =>
      assert(!rule.isApplicable(ex.untyped()))
    }
  }

  test("ValueRune correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k)
      assert(actual == expected)
    }
  }

}
