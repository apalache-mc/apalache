package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{
  BmcOper,
  TlaActionOper,
  TlaBoolOper,
  TlaTempOper
}
import com.google.inject.Inject

/**
  * An analysis that computes expression grades, which are used by the rewriter's caches.
  *
  * TODO: add tests
  *
  * @author Igor Konnov
  */
class ExprGradeAnalysis @Inject()(val store: ExprGradeStoreImpl) {
  private def update(e: TlaEx, grade: ExprGrade.Value): ExprGrade.Value = {
    store.store.update(e.ID, grade)
    grade
  }

  /**
    * Label all subexpressions of an expression with their grades. The grades are stored in the store.
    *
    * @param consts names that are treated as TLA+ constants
    * @param vars   names that are treated as TLA+ variables
    * @param expr   an expression to label
    */
  def labelExpr(
      consts: Set[String],
      vars: Set[String],
      expr: TlaEx
  ): ExprGrade.Value = {
    def eachExpr(e: TlaEx): ExprGrade.Value = e match {
      case ValEx(_) =>
        update(e, ExprGrade.Constant)

      case NameEx(name) =>
        if (consts.contains(name))
          update(e, ExprGrade.Constant)
        else if (vars.contains(name))
          update(e, ExprGrade.StateFree)
        else
          update(e, ExprGrade.StateBound)

      case OperEx(BmcOper.withType, annotated, _) =>
        // We forbid to cache type-annotated expressions.
        // Otherwise, {} <: {Int} would be cached as a set of integers, and then {} <: {{Int}} would be retrieved from
        // the cache as a set of integers, which is, obviously, not our intention
        update(e, ExprGrade.NonCacheable)
        update(annotated, ExprGrade.NonCacheable)

      case OperEx(TlaActionOper.prime, arg) =>
        // e.g., x'
        update(e, ExprGrade.join(ExprGrade.ActionFree, eachExpr(arg)))

      case OperEx(TlaTempOper.AA, _*) | OperEx(TlaTempOper.EE, _*) |
          OperEx(TlaTempOper.box, _*) | OperEx(TlaTempOper.diamond, _*) |
          OperEx(TlaTempOper.guarantees, _*) | OperEx(TlaTempOper.leadsTo, _*) |
          OperEx(TlaTempOper.strongFairness, _*) |
          OperEx(TlaTempOper.weakFairness, _*) =>
        e.asInstanceOf[OperEx].args.foreach(eachExpr)
        update(e, ExprGrade.Higher)

      case OperEx(_) =>
        update(e, ExprGrade.Constant)

      case OperEx(_, args @ _*) =>
        val grades = args map eachExpr
        update(e, grades reduce ExprGrade.join)

      case _ =>
        update(e, ExprGrade.Higher)
    }

    eachExpr(expr)
  }

  /**
    * Replace disjunctions with orParallel when the expression is action-level or higher.
    * @param expr a TLA+ expression
    * @return an updated expression, all grades are updated if needed.
    */
  def refineOrInExpr(expr: TlaEx): TlaEx = {
    expr match {
      case OperEx(TlaBoolOper.or, args @ _*) =>
        val newArgs = args map refineOrInExpr
        store.get(expr.ID) match {
          case Some(ExprGrade.Constant) | Some(ExprGrade.StateFree) |
              Some(ExprGrade.StateBound) =>
            expr // keep it

          case _ =>
            throw new RuntimeException("ExprGradeAnalysis is broken")
        }

      case OperEx(oper, args @ _*) =>
        OperEx(oper, args map refineOrInExpr: _*)

      case _ =>
        expr
    }
  }
}
