package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.formulas.Booleans.{BoolVar, True}
import at.forsyte.apalache.tla.lir.formulas.EUF.{UninterpretedLiteral, UninterpretedVar}
import at.forsyte.apalache.tla.lir.formulas.Integers.{IntLiteral, IntVar}
import at.forsyte.apalache.tla.lir.formulas.{Term, UninterpretedSort}
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, IntT1, SetT1, StrT1, TlaEx, TlaType1}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestValueRule extends AnyFunSuite {

  val rule: FormulaRule = new ValueRule

  val b: TlaType1 = BoolT1
  val i: TlaType1 = IntT1
  val aType: TlaType1 = ConstT1("A")
  val bType: TlaType1 = ConstT1("B")

  val intEx1: TBuilderInstruction = tla.int(1)
  val intEx2: TBuilderInstruction = tla.name("x", i)
  val intEx3: TBuilderInstruction = tla.plus(intEx1, intEx2)

  val boolEx1: TBuilderInstruction = tla.bool(true)
  val boolEx2: TBuilderInstruction = tla.name("p", b)
  val boolEx3: TBuilderInstruction = tla.and(boolEx1, boolEx2)

  val uninterpEx1: TBuilderInstruction = tla.constParsed("1_OF_A")
  val uninterpEx2: TBuilderInstruction = tla.name("v", bType)
  val uninterpEx3: TBuilderInstruction = tla.str("string")

  val expected: Map[TlaEx, Term] = Map(
      intEx1.build -> IntLiteral(1),
      intEx2.build -> IntVar("x"),
      boolEx1.build -> True,
      boolEx2.build -> BoolVar("p"),
      uninterpEx1.build -> UninterpretedLiteral("1", UninterpretedSort("A")),
      uninterpEx2.build -> UninterpretedVar("v", UninterpretedSort("B")),
      uninterpEx3.build -> UninterpretedLiteral("string", UninterpretedSort(StrT1.toString)),
  )

  test("ValueRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
    }

    val notApp = List(
        tla.and(tla.bool(true), tla.bool(false)),
        tla.impl(tla.name("x", BoolT1), tla.name("q", BoolT1)),
        tla.tuple(tla.int(1), tla.int(2)),
        tla.funSet(tla.name("S", SetT1(IntT1)), tla.dotdot(tla.int(1), tla.int(42))),
        tla.unchanged(tla.name("x", IntT1)),
        tla.forall(tla.name("x", IntT1), tla.name("S", SetT1(IntT1)), tla.name("p", BoolT1)),
    )

    notApp.foreach { ex =>
      assert(!rule.isApplicable(ex))
    }
  }

  test("ValueRune correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k).run(SmtDeclarations.init)._2
      assert(actual == expected)
    }
  }

}
