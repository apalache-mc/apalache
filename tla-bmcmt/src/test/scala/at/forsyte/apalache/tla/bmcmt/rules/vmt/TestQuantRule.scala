package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.bmcmt.RewriterException
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestQuantRule extends AnyFunSuite {

  val sType: TlaType1 = ConstT1("SSORT")
  val sSort: UninterpretedSort = UninterpretedSort("SSORT")

  val constSets: ConstSetMapT = Map("S" -> sSort)

  val rewriter: ToTermRewriter = ToTermRewriterImpl(constSets)

  val rule: FormulaRule = new QuantifierRule(rewriter, new RestrictedSetJudgement(constSets))

  val b: TlaType1 = BoolT1

  val p: TBuilderInstruction = tla.name("p", b)
  val pVar: Term = BoolVar("p")
  val q: TBuilderInstruction = tla.name("q", b)
  val qVar: Term = BoolVar("q")

  val x: TBuilderInstruction = tla.name("x", sType)
  val y: TBuilderInstruction = tla.name("y", IntT1)
  val set: TBuilderInstruction = tla.name("S", SetT1(sType))
  val intSet: TBuilderInstruction = tla.intSet()

  val expected: Map[TlaEx, BoolExpr] = Map(
      tla.exists(x, set, p).build -> Exists(List(("x", sSort)), pVar),
      tla.forall(y, intSet, q).build -> Forall(List(("y", IntSort)), qVar),
  )

  test("QuantRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
    }

    assertThrows[RewriterException] {
      val tType = ConstT1("TSORT")
      rule(tla.exists(tla.name("t", tType), tla.name("T", SetT1(tType)), p))
    }

    val notApp = List(
        tla.tuple(tla.int(1), tla.int(2)),
        tla.funSet(tla.name("S", SetT1(IntT1)), tla.dotdot(tla.int(1), tla.int(42))),
        tla.unchanged(tla.name("x", IntT1)),
        tla.and(tla.name("x", BoolT1), tla.name("T", BoolT1), tla.name("p", BoolT1)),
        tla.int(2),
        tla.bool(true),
    )

    notApp.foreach { ex =>
      assert(!rule.isApplicable(ex))
    }
  }

  test("QuantRule correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k).run(SmtDeclarations.init)._2
      assert(actual == expected)
    }
  }
}
