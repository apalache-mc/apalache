package at.forsyte.apalache.tla.lir

/**
  * TLA+ operators.
  */
package oper {

  /**
    * The levels of the operators as defined in the TLA+ book:
    * Constant (contains only primitive operations and constants), State (reasons about current state),
    * Action (reasons about a pair of states), and Temporal (reasons about executions).
    */
  object Level extends Enumeration {
    val Constant, State, Action, Temporal = Value
  }

  /**
    * Interpretation shows how standard an operator is: Predefined (fixed interpretation),
    * StandardLib (many standard interpretations), User (user-defined).
    */
  object Interpretation extends Enumeration {
    /** this operator has a fixed and the only interpretation in TLA+, e.g., \cup, \cap. */
    val Predefined: Interpretation.Value = Value
    /** this operator has some interpretation defined in a standard module, e.g., Integers!+, Real!+. */
    val StandardLib: Interpretation.Value = Value
    /** this operator is defined by the user and unknown to TLA+ */
    val User: Interpretation.Value = Value
    /** this operator does not have any definition but is used as a signature, e.g., f(_, _) in operator parameters */
    val Signature: Interpretation.Value = Value
  }

  class OperArity(private val m_cond: Int => Boolean) extends Serializable {
    def cond(n: Int): Boolean = if (n < 0) false else m_cond(n)

    def &&(other: OperArity): OperArity = new OperArity(i => m_cond(i) && other.m_cond(i))

    def ||(other: OperArity): OperArity = new OperArity(i => m_cond(i) || other.m_cond(i))

    def unary_! : OperArity = new OperArity(!m_cond(_))
  }

  sealed case class MinimalArity(n: Int) extends OperArity(_ >= n)

  sealed case class AnyArity() extends OperArity(_ => true)

  sealed case class FixedArity(n: Int) extends OperArity(_ == n)

  sealed case class AnyOddArity() extends OperArity(_ % 2 == 1)

  sealed case class AnyEvenArity() extends OperArity(_ % 2 == 0)

  sealed case class AnyPositiveArity() extends OperArity(_ > 0)
}
