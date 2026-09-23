package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.{TlaType1, VarT1}
import at.forsyte.apalache.tla.typecheck.etc.ConstraintSolver.TypeReport
import at.forsyte.apalache.tla.types.{EqClass, Substitution, TypeUnifier, TypeVarPool}

/**
 * A constraint solver that collects a series of equations and solves them with the type unification algorithm.
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

  // Reporting must not add equations: that would affect isFreeVar and hence generalization.
  /** Add a success callback that can be deferred and refined across LET scopes. */
  private[etc] def addTypeReport(tt: TlaType1)(notify: TlaType1 => Unit): Unit = {
    typesToReport :+= TypeReport(tt, notify)
  }

  /** After a successful local solve, pass reports that still depend on the enclosing context to its solver. */
  private[etc] def reportTypesTo(parent: ConstraintSolver, sharedVars: Set[Int]): Unit = {
    val sharedNames = sharedVars.flatMap(v => solution.subRec(VarT1(v)).usedNames)
    for (report <- typesToReport) {
      val resolved = report.resolve(solution)
      // Preserve variables that an enclosing solver may still refine, including variables newly exposed by
      // local solutions. Everything else belongs to this definition and must survive further specialization.
      val refinable = resolved.tt.usedNames & sharedNames
      if (refinable.isEmpty) {
        resolved.emit(resolved.tt)
      } else {
        parent.typesToReport :+= resolved.copy(frozenVars = resolved.frozenVars ++ (resolved.tt.usedNames -- refinable))
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

  // LET definitions defer success callbacks until reportTypesTo can determine which types are final.
  def solve(reportTypes: Boolean = true): Option[Substitution] = {
    val isDefined = solvePartially().isDefined

    if (isDefined && constraints.isEmpty) {
      if (reportTypes) {
        for (report <- typesToReport) {
          val resolved = report.resolve(solution)
          resolved.emit(resolved.tt)
        }
        typesToReport = List.empty
      }

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

  /**
   * Test whether a variable is free in the context that is induced by the solved constraints.
   *
   * @param varNo
   *   a variable number
   * @return
   *   true if the variable occurs in the partial solution of the solver
   */
  def isFreeVar(varNo: Int): Boolean = {
    def outsideClass(cls: EqClass): Boolean = !cls.typeVars.contains(varNo)
    // Check both the approximate solution, which the solver was initialized with, and the solution, if it exists.
    // This is probably a computationally expensive check:
    // https://github.com/apalache-mc/apalache/issues/973
    approximateSolution.mapping.keySet.forall(outsideClass) && solution.mapping.keySet.forall(outsideClass)
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
  // A report may outlive the solver of its definition. Only its still-shared variables can then be refined.
  private case class TypeReport(tt: TlaType1, emit: TlaType1 => Unit, frozenVars: Set[Int] = Set.empty) {
    def resolve(sub: Substitution): TypeReport = {
      if (frozenVars.isEmpty) {
        copy(tt = sub.subRec(tt))
      } else {
        val scoped = Substitution((tt.usedNames -- frozenVars).map(v => EqClass(v) -> sub.subRec(VarT1(v))).toMap)
        copy(tt = scoped.subRec(tt))
      }
    }
  }
}
