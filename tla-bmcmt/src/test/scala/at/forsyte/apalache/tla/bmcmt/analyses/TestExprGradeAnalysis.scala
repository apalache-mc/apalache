package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, OperEx, TlaEx}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestExprGradeAnalysis extends AnyFunSuite {
  private case class AnalysisResult(expr: TlaEx, grade: ExprGrade.Value, store: ExprGradeStoreImpl)

  private def analyze(
      instruction: TBuilderInstruction,
      consts: Set[String] = Set.empty,
      vars: Set[String] = Set.empty): AnalysisResult = {
    val expr = instruction.build
    val store = new ExprGradeStoreImpl
    val grade = new ExprGradeAnalysis(store).labelExpr(consts, vars, expr)
    AnalysisResult(expr, grade, store)
  }

  test("classifies values and names") {
    assert(analyze(tla.int(1)).grade == ExprGrade.Constant)
    assert(analyze(tla.name("C", IntT1), consts = Set("C")).grade == ExprGrade.Constant)
    assert(analyze(tla.name("x", IntT1), vars = Set("x")).grade == ExprGrade.StateFree)
    assert(analyze(tla.name("i", IntT1)).grade == ExprGrade.StateBound)
  }

  test("joins grades across ordinary operators and records child grades") {
    val result = analyze(tla.eql(tla.name("x", IntT1), tla.int(1)), vars = Set("x"))

    assert(result.grade == ExprGrade.StateFree)
    assert(result.store.get(result.expr.ID).contains(ExprGrade.StateFree))
    result.expr match {
      case OperEx(_, stateVar, literal) =>
        assert(result.store.get(stateVar.ID).contains(ExprGrade.StateFree))
        assert(result.store.get(literal.ID).contains(ExprGrade.Constant))
      case unexpected =>
        fail(s"Expected an operator expression, found: $unexpected")
    }
  }

  test("distinguishes free and bound action expressions") {
    val freeAction = tla.prime(tla.name("x", IntT1))
    val boundAction = tla.prime(tla.name("i", IntT1))

    assert(analyze(freeAction, vars = Set("x")).grade == ExprGrade.ActionFree)
    assert(analyze(boundAction).grade == ExprGrade.ActionBound)
  }

  test("classifies temporal expressions as higher and visits their arguments") {
    val result = analyze(tla.box(tla.name("x", BoolT1)), vars = Set("x"))

    assert(result.grade == ExprGrade.Higher)
    result.expr match {
      case OperEx(_, stateVar) =>
        assert(result.store.get(stateVar.ID).contains(ExprGrade.StateFree))
      case unexpected =>
        fail(s"Expected an operator expression, found: $unexpected")
    }
  }

  test("classifies generated values as non-cacheable") {
    assert(analyze(tla.gen(tla.int(1), IntT1)).grade == ExprGrade.NonCacheable)
  }

  test("classifies nullary operators as constant") {
    assert(analyze(tla.and()).grade == ExprGrade.Constant)
  }

  test("joins expression grades") {
    val cases = Seq(
        (ExprGrade.Constant, ExprGrade.StateFree, ExprGrade.StateFree),
        (ExprGrade.StateFree, ExprGrade.StateBound, ExprGrade.StateBound),
        (ExprGrade.ActionFree, ExprGrade.StateBound, ExprGrade.ActionBound),
        (ExprGrade.Higher, ExprGrade.Constant, ExprGrade.Higher),
        (ExprGrade.NonCacheable, ExprGrade.Higher, ExprGrade.NonCacheable),
    )

    cases.foreach { case (left, right, expected) =>
      assert(ExprGrade.join(left, right) == expected)
      assert(ExprGrade.join(right, left) == expected)
    }
  }

  test("classifies unsupported expression forms as higher") {
    val letIn = tla.letIn(tla.bool(true), tla.decl("A", tla.bool(true)))

    assert(analyze(letIn).grade == ExprGrade.Higher)
  }
}
