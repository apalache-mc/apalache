package at.forsyte.apalache.tla.lir.oper

/**
 * A temporal operator.
 */
abstract class TlaTempOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaTempOper {

  /**
   * The LTL box operator: `[]P`.
   */
  object box extends TlaTempOper {
    override val name: String = "GLOBALLY"

    override def arity: OperArity = FixedArity(1)

    override val precedence: (Int, Int) = (4, 15)
  }

  /**
   * The LTL diamond operator: `<>P`.
   */
  object diamond extends TlaTempOper {
    override val name: String = "EVENTUALLY"

    override def arity: OperArity = FixedArity(1)

    override val precedence: (Int, Int) = (4, 15)
  }

  /**
   * The leads-to operator: `P ~> Q`.
   */
  object leadsTo extends TlaTempOper {
    override val name: String = "LEADS_TO"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (2, 2)
  }

  /**
   * The 'guarantees' operator: `P -+-> Q`.
   */
  object guarantees extends TlaTempOper {
    override val name: String = "GUARANTEES"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (2, 2)
  }

  /**
   * The weak fairness operator: `WF_x(A)`. The argument order is: (x, A).
   */
  object weakFairness extends TlaTempOper {
    override val name: String = "WEAK_FAIRNESS"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (4, 15)
  }

  /**
   * The strong fairness operator: `SF_x(A)`. The argument order is: (x, A)
   */
  object strongFairness extends TlaTempOper {
    override val name: String = "STRONG_FAIRNESS"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (4, 15)
  }

  /**
   * The temporal existential quantification (hiding) operator: `\EE x: P`.
   */
  object EE extends TlaTempOper {
    override val name: String = "TEMPORAL_EXISTS"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (0, 0) // Sec 15.2.1, Undelimited Constructs
  }

  /**
   * The temporal universal quantification operator: `\AA x: P`.
   */
  object AA extends TlaTempOper {
    override val name: String = "TEMPORAL_FORALL"

    override def arity: OperArity = FixedArity(2)

    override val precedence: (Int, Int) = (0, 0) // Sec 15.2.1, Undelimited Constructs
  }
}
