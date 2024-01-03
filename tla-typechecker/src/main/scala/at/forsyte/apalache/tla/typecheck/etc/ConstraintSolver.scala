package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.lir.TlaType1
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
  private var typesToReport: List[(Clause, TlaType1)] = List.empty

  def addConstraint(constraint: Clause): Unit = {
    constraints = constraints :+ constraint
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
            typesToReport :+= (cons, solution.subRec(typ))
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

  def solve(): Option[Substitution] = {
    val isDefined = solvePartially().isDefined

    if (isDefined && constraints.isEmpty) {
      // all constraints have been solved, report the types
      for ((c, t) <- typesToReport) {
        c.onTypeFound(solution.subRec(t))
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
    // https://github.com/informalsystems/apalache/issues/973
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
