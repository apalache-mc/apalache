package at.forsyte.apalache.tla.lir.oper

/**
 * Boolean operators.
 *
 * TODO: rename it to TlaLogicOper?
 */
abstract class TlaBoolOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaBoolOper {

  /**
   * A conjunction over an arbitrary number of arguments.
   * By convention, it should be evaluated to TRUE, when the argument list is empty.
   * Note that TLC interprets a conjunction A /\ B as IF A THEN B ELSE FALSE.
   */
  object and extends TlaBoolOper {
    override def arity = AnyArity()
    override val name = "AND"
    override val precedence: (Int, Int) = (3, 3)
  }

  /**
   * A disjunction over an arbitrary number of arguments.
   * By convention, it should be evaluated to FALSE, when the argument list is empty.
   * Note that TLC interprets a state-level disjunction A \/ B as
   * IF A THEN TRUE ELSE B.
   */
  object or extends TlaBoolOper {
    override def arity: OperArity = AnyArity()

    override val name: String = "OR"
    override val precedence: (Int, Int) = (3, 3)
  }

  /**
   * A negation.
   */
  object not extends TlaBoolOper {
    override def arity: OperArity = FixedArity(1)

    override val name: String = "NOT"
    override val precedence: (Int, Int) = (4, 4)
  }

  /**
   * An implication A => B. For all the purposes, it should be thought of as being equivalent to ~A \/ B.
   */
  object implies extends TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "IMPLIES"
    override val precedence: (Int, Int) = (1, 1)
  }

  /**
   * An equivalence A <=> B.
   */
  object equiv extends TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "EQUIV"
    override val precedence: (Int, Int) = (2, 2)
  }

  /**
   * A universal quantifier over a set: `\A x \in S : p`.
   */
  object forall extends TlaBoolOper {
    override def arity: OperArity = FixedArity(3)

    override val name: String = "FORALL3"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /**
   * A universal quantifier over the whole universe: `\A x : p`.
   */
  object forallUnbounded extends TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "FORALL2"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /**
   * An existential quantifier over a set: `\E x \in S : p`.
   */
  object exists extends TlaBoolOper {
    override def arity: OperArity = FixedArity(3)

    override val name: String = "EXISTS3"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /**
   * An existential quantifier over the whole universe: `\E x : p`.
   */
  object existsUnbounded extends TlaBoolOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "EXISTS2"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }
}
