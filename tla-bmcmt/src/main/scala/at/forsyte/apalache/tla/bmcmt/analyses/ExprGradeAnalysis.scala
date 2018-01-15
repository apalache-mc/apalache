package at.forsyte.apalache.tla.bmcmt.analyses

import at.forsyte.apalache.tla.assignments.SpecWithTransitions
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.temporal.TlaTempOper
import com.google.inject.Inject

/**
  * An analysis that computes expression grades.
  *
  * TODO: add tests
  *
  * @author Igor Konnov
  */
class ExprGradeAnalysis @Inject()(val store: ExprGradeStoreImpl) {
  /**
    * Label all subexpressions of an expression with their grades.
    *
    * @param rootModule a module that contains all declarations
    * @param expr       an expression to label
    */
  def labelWithGrades(rootModule: TlaModule, expr: TlaEx): Unit = {
    val consts = Set(rootModule.constDeclarations.map(_.name): _*)
    val vars = Set(rootModule.varDeclarations.map(_.name): _*)

    def add(e: TlaEx, grade: ExprGrade.Value): ExprGrade.Value = {
      store.store += (e.ID -> grade)
      grade
    }

    def eachExpr(e: TlaEx): ExprGrade.Value = e match {
      case ValEx(_) =>
        add(e, ExprGrade.Constant)

      case NameEx(name) =>
        if (consts.contains(name))
          add(e, ExprGrade.Constant)
        else if (vars.contains(name))
          add(e, ExprGrade.ActionFree)
        else
          add(e, ExprGrade.ActionBound)

      case OperEx(TlaTempOper.AA, _*) | OperEx(TlaTempOper.EE, _*)
           | OperEx(TlaTempOper.box, _*) | OperEx(TlaTempOper.diamond, _*)
           | OperEx(TlaTempOper.guarantees, _*) | OperEx(TlaTempOper.leadsTo, _*)
           | OperEx(TlaTempOper.strongFairness, _*)
           | OperEx(TlaTempOper.weakFairness, _*) =>
        e.asInstanceOf[OperEx].args.foreach(eachExpr)
        add(e, ExprGrade.Higher)

      case OperEx(_) =>
        add(e, ExprGrade.Constant)

      case OperEx(_, args@_*) =>
        val grades = args map eachExpr
        add(e, grades reduce ExprGrade.join)

      case _ =>
        add(e, ExprGrade.Higher)
    }

    eachExpr(expr)
  }

  def labelWithGrades(spec: SpecWithTransitions): Unit = {
    spec.initTransitions.foreach(e => labelWithGrades(spec.rootModule, e))
    spec.nextTransitions.foreach(e => labelWithGrades(spec.rootModule, e))
    spec.notInvariant.foreach(e => labelWithGrades(spec.rootModule, e))
  }
}
