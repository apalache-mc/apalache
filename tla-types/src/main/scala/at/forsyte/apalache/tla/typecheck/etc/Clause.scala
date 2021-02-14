package at.forsyte.apalache.tla.typecheck.etc

import at.forsyte.apalache.tla.typecheck.{TlaType1, VarT1}

/**
 * A unification constraint for the unification solver.
 * Normally, unification solvers are conjunctive. But TLA+ requires operators overloading.
 * Thus, our constraints admit disjunctions.
 */
sealed abstract class Clause {

  /**
   * A callback for registering the type when it is known precisely
   */
  var onTypeFound: TlaType1 => Unit = (_ => ())

  /**
   * A callback for registering a type error when it occurs
   */
  var onTypeError: Seq[TlaType1] => Unit = (_ => ())

  def setOnTypeFound(callback: TlaType1 => Unit): Clause = {
    onTypeFound = callback
    this
  }

  def setOnTypeError(callback: Seq[TlaType1] => Unit): Clause = {
    onTypeError = callback
    this
  }
}

/**
 * An equation: the left argument should be equal to the right argument.
 *
 * @param unknown a variable in the left-hand side of the equation
 * @param term a type in the right-hand side of the equation
 */
case class EqClause(unknown: VarT1, term: TlaType1) extends Clause

/**
 * A disjunctive clause: one of the argument equations should hold true.
 * Such a clause is produced by an overloaded TLA+ operator.
 *
 * @param clauses the clauses to choose from.
 */
case class OrClause(clauses: EqClause*) extends Clause
