package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{TlaType1, VarT1}
import at.forsyte.apalache.tla.typecheck.etc.ConstraintSolver.TypeReport
import at.forsyte.apalache.tla.types.{EqClass, Substitution, TypeUnifier, TypeVarPool}

/**
 * A constraint solver that collects a series of equations and solves them with the type unification algorithm.
 *
 * When the solver finds the type of a clause, it records a type report. Once all constraints are solved, [[solve]]
 * applies the solution to the reports and sends them to their callbacks. The type checker solves every LET definition
 * with a separate solver, and some types in the definition may contain type variables of the enclosing context. The
 * enclosing solver can still refine these variables. Hence, the solver of a definition calls [[solveDeferringReports]]
 * and then [[reportTypesTo]], which sends the final reports and passes the others to the enclosing solver.
 *
 * @author
 *   Igor Konnov
 */
class ConstraintSolver(varPool: TypeVarPool, approximateSolution: Substitution = Substitution.empty) {
  private var solution: Substitution = approximateSolution
  private var constraints: List[Clause] = List.empty
  private var typesToReport: List[TypeReport] = List.empty

  def addConstraint(constraint: Clause): Unit = {
    constraints = constraints :+ constraint
  }

  /**
   * Send the type `tt` to `callback`, once it is final. Unlike a clause, a report does not add equations. Hence, it
   * does not change the solution.
   */
  private[etc] def addTypeReport(tt: TlaType1)(callback: TlaType1 => Unit): Unit = {
    addReport(TypeReport(tt, callback))
  }

  /**
   * Hand over the type reports after [[solveDeferringReports]]. A report is final, unless it contains a type variable
   * that the solution assigns to a shared variable. Send the final reports, and pass the others to `parent`.
   *
   * @param parent
   *   the solver of the enclosing context
   * @param sharedVars
   *   the type variables that the definition shares with the enclosing context
   */
  private[etc] def reportTypesTo(parent: ConstraintSolver, sharedVars: Set[Int]): Unit = {
    val sharedNames = sharedVars.flatMap(v => solution.subRec(VarT1(v)).usedNames)
    for (report <- typesToReport) {
      val resolved = report.resolve(solution)
      val refinable = resolved.tt.usedNames & sharedNames
      if (refinable.isEmpty) {
        resolved.send()
      } else {
        // The other variables belong to the definition. The enclosing solver must not refine them.
        parent.addReport(resolved.copy(frozenVars = resolved.frozenVars ++ (resolved.tt.usedNames -- refinable)))
      }
    }
    typesToReport = List.empty
  }

  def solvePartially(): Option[Substitution] = {
    var progress = true
    while (constraints.nonEmpty && progress) {
      var postponed: List[Clause] = List.empty
      progress = false

      for (cons <- constraints) {
        solveOne(solution, cons) match {
          case Some((uniqueSolution, typ)) =>
            progress = true
            solution = uniqueSolution
            addTypeReport(solution.subRec(typ))(cons.onTypeFound)
          case None =>
            cons match {
              case OrClause(_ @_*) =>
                // no solution for a disjunctive constraint:
                // try to resolve the unit constraints and postpone the disjunctive one for later
                postponed = postponed :+ cons

              case EqClause(_, term) =>
                // no solution for a unit constraint:
                // flag an error immediately
                cons.onTypeError(solution, Seq(solution.subRec(term)))
                // reset the constraints, so they are not reported later
                constraints = List.empty
                typesToReport = List.empty
                return None
            }
        }
      }

      // solve the postponed constraints at the next iteration
      constraints = postponed
    }

    // return the partial solution
    Some(solution)
  }

  /**
   * Solve all constraints and send the type reports.
   *
   * @return
   *   the solution, if all constraints are solved; None, otherwise
   */
  def solve(): Option[Substitution] = {
    val result = solveDeferringReports()
    if (result.isDefined) {
      typesToReport.foreach(_.resolve(solution).send())
      typesToReport = List.empty
    }
    result
  }

  /**
   * Solve all constraints like [[solve]], but keep the type reports for [[reportTypesTo]].
   *
   * @return
   *   the solution, if all constraints are solved; None, otherwise
   */
  private[etc] def solveDeferringReports(): Option[Substitution] = {
    val isDefined = solvePartially().isDefined

    if (isDefined && constraints.isEmpty) {
      Some(solution)
    } else {
      constraints.foreach {
        case c @ OrClause(clauses @ _*) =>
          val partialSignatures = clauses.map { c => solution.subRec(c.term) }
          c.onTypeError(solution, partialSignatures)

        case c @ EqClause(_, term) =>
          c.onTypeError(solution, Seq(solution.subRec(term)))
      }
      typesToReport = List.empty
      None
    }
  }

  private def addReport(report: TypeReport): Unit = {
    typesToReport :+= report
  }

  private def solveOne(solution: Substitution, constraint: Clause): Option[(Substitution, TlaType1)] = {
    constraint match {
      case EqClause(unknown, term) =>
        // If there is a solution, we return it. We ignore the type, as it should be bound to `unknown`.
        new TypeUnifier(varPool).unify(solution, unknown, term)

      case OrClause(eqs @ _*) =>
        // try to solve a disjunctive clause
        eqs.flatMap(solveOne(solution, _)) match {
          case Seq(uniqueSolution) => Some(uniqueSolution)
          case _                   => None
        }
    }
  }
}

object ConstraintSolver {

  /**
   * A type to send to `callback`, once it is final.
   *
   * @param frozenVars
   *   the type variables that must not be substituted anymore. When the solver of a LET definition passes a report to
   *   the enclosing solver, it freezes the variables that the definition does not share with the enclosing context. The
   *   definition has either generalized them, or they occur only inside the definition. Normally, the enclosing solver
   *   never sees these variables, since every use of a definition instantiates its type with fresh variables. The
   *   exception is an operator passed by name, e.g., `K` in `Apply(K, 1)`: the case of `EtcName` in [[EtcTypeChecker]]
   *   does not instantiate the type, so the enclosing solver may bind the generalized variables of `K`. Freezing keeps
   *   the reported types consistent with the generalized signature of the definition.
   */
  private case class TypeReport(tt: TlaType1, callback: TlaType1 => Unit, frozenVars: Set[Int] = Set.empty) {

    /** Apply the substitution to the variables that are not frozen. */
    def resolve(sub: Substitution): TypeReport = {
      if (frozenVars.isEmpty) {
        copy(tt = sub.subRec(tt))
      } else {
        val scoped = Substitution((tt.usedNames -- frozenVars).map(v => EqClass(v) -> sub.subRec(VarT1(v))).toMap)
        copy(tt = scoped.subRec(tt))
      }
    }

    def send(): Unit = callback(tt)
  }
}
