package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck.TlaType1

/**
  * A constraint solver that collects a series of equations and solves them with the type unification algorithm.
  *
  * @author Igor Konnov
  */
class ConstraintSolver(approximateSolution: Substitution = Substitution.empty) {
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
        val result = solveOne(solution, cons)
        if (result.isDefined) {
          // there is a unique solution
          progress = true
          solution = result.get._1
          typesToReport :+= (cons, solution(result.get._2))
        } else {
          cons match {
            case OrClause(_@_*) =>
              // no solution for a disjunctive constraint:
              // try to resolve the unit constraints and postpone the disjunctive one for later
              postponed = postponed :+ cons

            case EqClause(_, term) =>
              // no solution for a unit constraint:
              // flag an error immediately
              cons.onTypeError(Seq(solution(term)))
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
        c.onTypeFound(solution(t))
      }

      Some(solution)
    } else {
      constraints.foreach {
        case c @ OrClause(clauses @ _*) =>
          val partialSignatures = clauses.map { c => solution(c.term) }
          c.onTypeError(partialSignatures)

        case c @ EqClause(_, term) =>
          c.onTypeError(Seq(solution(term)))
      }
      None
    }
  }

  private def solveOne(solution: Substitution, cons: Clause): Option[(Substitution, TlaType1)] = {
    cons match {
      case EqClause(unknown, term) =>
        // If there is a solution, we return it. We ignore the type, as it should be bound to `unknown`.
        new TypeUnifier().unify(solution, unknown, term)

      case OrClause(eqs @ _*) =>
        // try to solve a disjunctive clause
        eqs.flatMap(solveOne(solution, _)) match {
          case Seq(uniqueSolution) => Some(uniqueSolution)
          case _noneOrAmbiguous => None
        }
    }
  }
}
