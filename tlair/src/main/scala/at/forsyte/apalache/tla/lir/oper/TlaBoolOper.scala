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
  val and = new TlaBoolOper {
    override def arity = AnyArity()
    override val name = "/\\"
    override val precedence: (Int, Int) = (3, 3)
  }

  /**
    * A disjunction over an arbitrary number of arguments.
    * By convention, it should be evaluated to FALSE, when the argument list is empty.
    * Note that TLC interprets a state-level disjunction A \/ B as
    * IF A THEN TRUE ELSE B.
    */
  val or = new TlaBoolOper {
    override def arity: OperArity = AnyArity()
    override val name: String = "\\/"
    override val precedence: (Int, Int) = (3, 3)
  }

  /**
    * A negation.
    */
  val not = new TlaBoolOper {
    override def arity: OperArity = FixedArity(1)
    override val name: String = "~"
    override val precedence: (Int, Int) = (4, 4)
  }

  /**
    * An implication A => B. For all the purposes, it should be thought of as being equivalent to ~A \/ B.
    */
  val implies = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "=>"
    override val precedence: (Int, Int) = (1, 1)
  }

  /**
    * An equivalence A <=> B.
    */
  val equiv = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "<=>"
    override val precedence: (Int, Int) = (2, 2)
  }

  /** \A x \in S : p */
  val forall = new TlaBoolOper {
    override def arity: OperArity = FixedArity(3)
    override val name: String = "\\A3"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /** \A x : p */
  val forallUnbounded = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "\\A2"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /** \E x \in S : p */
  val exists = new TlaBoolOper {
    override def arity: OperArity = FixedArity(3)
    override val name: String = "\\E3"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /** \E x : p */
  val existsUnbounded = new TlaBoolOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "\\E2"
    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }
}
