/**
  * Here we group auxiliary classes that we use as flags in the translation process.
  */
package at.forsyte.apalache.tla.imp

/**
  * A type of the operator definition.
  */
sealed abstract class RecursionStatus

/**
  * Expressions are translated outside a recursive definition.
  */
case class OutsideRecursion() extends RecursionStatus

/**
  * Expressions are translated inside a recursive definition.
  */
case class InsideRecursion() extends RecursionStatus
