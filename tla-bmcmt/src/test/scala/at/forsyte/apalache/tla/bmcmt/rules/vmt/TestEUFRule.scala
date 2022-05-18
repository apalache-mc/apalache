package at.forsyte.apalache.tla.bmcmt.rules.vmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, SetT1, TlaEx, TupT1}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.formulas.Booleans._
import at.forsyte.apalache.tla.lir.formulas.EUF.{Apply, Equal, FunDef, FunctionVar, ITE}
import at.forsyte.apalache.tla.lir.formulas._
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestEUFRule extends AnyFunSuite {

  val sType = ConstT1("SSORT")
  val sSort = UninterpretedSort("SSORT")

  val constSets = Map("S" -> sSort)

  val rewriter = ToTermRewriterImpl(constSets)

  val funName = "f"
  val constGen = new UniqueNameGenerator {
    override def newName(): String = funName
  }
  val fType = FunT1(TupT1(sType, IntT1), sType)
  val f = tla.name(funName).as(fType)

  val rule = new EUFRule(rewriter, new RestrictedSetJudgement(constSets), constGen)

  val b = BoolT1

  val p = tla.name("p").as(b)
  val pVar = BoolVar("p")
  val q = tla.name("q").as(b)
  val qVar = BoolVar("q")

  val x = tla.name("x").as(sType)
  val xVar = mkVariable("x", sSort)
  val xPrimeVar = mkVariable(VMTprimeName("x"), sSort)
  val y = tla.name("y").as(IntT1)
  val set = tla.name("S").as(SetT1(sType))
  val intSet = tla.intSet().as(SetT1(IntT1))

  val expected: Map[TlaEx, Term] = Map(
      tla.assign(tla.prime(x).as(sType), x).as(b) -> Equal(xPrimeVar, xVar),
      tla.eql(x, x).as(b) -> Equal(xVar, xVar),
      tla.ite(p, p, q).as(b) -> ITE(pVar, pVar, qVar),
      tla.funDef(x, x, set, y, intSet).as(fType) ->
        FunDef(funName, List(("x", sSort), ("y", IntSort())), xVar),
      tla.appFun(f, tla.tuple(x, y).as(fType.arg)).as(fType.res) ->
        Apply(FunctionVar(funName, FunctionSort(sSort, sSort, IntSort())), xVar, mkVariable("y", IntSort())),
  )

  test("EUFRule applicability") {
    expected.keys.foreach { ex =>
      assert(rule.isApplicable(ex))
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

  test("EUFRule correctness") {
    expected.foreach { case (k, expected) =>
      val actual = rule(k)
      assert(actual == expected)
    }
  }
}
