package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, SetT1, TlaEx, TlaType1, TupT1}
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, DefineFun, Equal, FunctionVar, ITE}
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestEUFRule extends AnyFunSuite {

  val sType: TlaType1 = ConstT1("SSORT")
  val sSort: UninterpretedSort = UninterpretedSort("SSORT")

  val constSets: ConstSetMapT = Map("S" -> sSort)

  val rewriter: ToTermRewriter = ToTermRewriterImpl(constSets)

  val funName: String = "f"
  val constGen: UniqueNameGenerator = new UniqueNameGenerator {
    override def newName(): String = funName
  }
  val fType: TlaType1 = FunT1(TupT1(sType, IntT1), sType)
  val f: TBuilderInstruction = tla.name(funName, fType)

  val rule: FormulaRule = new EUFRule(rewriter, new RestrictedSetJudgement(constSets), constGen)

  val b: TlaType1 = BoolT1

  val p: TBuilderInstruction = tla.name("p", b)
  val pVar: Term = BoolVar("p")
  val q: TBuilderInstruction = tla.name("q", b)
  val qVar: Term = BoolVar("q")

  val x: TBuilderInstruction = tla.name("x", sType)
  val xVar: Term = mkVariable("x", sSort)
  val xPrimeVar: Term = mkVariable(VMTprimeName("x"), sSort)
  val y: TBuilderInstruction = tla.name("y", IntT1)
  val set: TBuilderInstruction = tla.name("S", SetT1(sType))
  val intSet: TBuilderInstruction = tla.intSet()

  val expected: Map[TlaEx, Term] = Map(
      tla.assign(tla.prime(x), x).build -> Equal(xPrimeVar, xVar),
      tla.eql(x, x).build -> Equal(xVar, xVar),
      tla.ite(p, p, q).build -> ITE(pVar, pVar, qVar),
      tla.funDef(x, x -> set, y -> intSet).build ->
        DefineFun(funName, List(("x", sSort), ("y", IntSort)), xVar).asVar,
      tla.app(f, tla.tuple(x, y)).build ->
        Apply(FunctionVar(funName, FunctionSort(sSort, sSort, IntSort)), xVar, mkVariable("y", IntSort)),
  )

  test("EUFRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
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

  test("EUFRule correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k).run(SmtDeclarations.init)._2
      assert(actual == expected)
    }
  }
}
