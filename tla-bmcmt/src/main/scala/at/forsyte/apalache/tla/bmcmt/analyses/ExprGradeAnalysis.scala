package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{ApalacheOper, TlaActionOper, TlaTempOper}
import com.google.inject.Inject

/**
 * An analysis that computes expression grades, which are used by the rewriter's caches.
 * @author
 *   Igor Konnov
 */
class ExprGradeAnalysis @Inject()(store: ExprGradeStoreImpl) {
  private def update(e: TlaEx, grade: ExprGrade.Value): ExprGrade.Value = {
    store.put(e.ID, grade)
    grade
  }

  /**
   * Label all subexpressions of an expression with their grades. The grades are stored in the store.
   *
   * @param consts
   *   names that are treated as TLA+ constants
   * @param vars
   *   names that are treated as TLA+ variables
   * @param expr
   *   an expression to label
   */
  def labelExpr(consts: Set[String], vars: Set[String], expr: TlaEx): ExprGrade.Value = {
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

      case OperEx(ApalacheOper.gen, _) =>
        // Apalache!Gen(n) should not be cached, as it produces a new set of constants on each call
        update(e, ExprGrade.NonCacheable)

      case OperEx(TlaActionOper.prime, arg) =>
        // e.g., x'
        update(e, ExprGrade.join(ExprGrade.ActionFree, eachExpr(arg)))

      case OperEx(TlaTempOper.AA, _*) | OperEx(TlaTempOper.EE, _*) | OperEx(TlaTempOper.box, _*) |
          OperEx(TlaTempOper.diamond, _*) | OperEx(TlaTempOper.guarantees, _*) | OperEx(TlaTempOper.leadsTo, _*) |
          OperEx(TlaTempOper.strongFairness, _*) | OperEx(TlaTempOper.weakFairness, _*) =>
        e.asInstanceOf[OperEx].args.foreach(eachExpr)
        update(e, ExprGrade.Higher)

      case OperEx(_) =>
        update(e, ExprGrade.Constant)

      case OperEx(_, args @ _*) =>
        val grades = args.map(eachExpr)
        update(e, grades.reduce(ExprGrade.join))

      case _ =>
        update(e, ExprGrade.Higher)
    }

    eachExpr(expr)
  }
}
