package at.forsyte.apalache.tla.lir.oper

/**
 * A temporal operator.
 */
abstract class TlaTempOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaTempOper {

  /** The LTL box operator */
  object box extends TlaTempOper {
    override val name: String = "[]"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (4, 15)
  }

  /** The LTL diamond operator */
  object diamond extends TlaTempOper {
    override val name: String = "<>"
    override def arity: OperArity = FixedArity(1)
    override val precedence: (Int, Int) = (4, 15)
  }

  /** The leads-to operator */
  object leadsTo extends TlaTempOper {
    override val name: String = "~>"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (2, 2)
  }

  /** The 'guarantees' operator */
  object guarantees extends TlaTempOper {
    override val name: String = "-+->"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (2, 2)
  }

  /**
   * The weak fairness operator WF_x(A). The argument order is: (x, A).
   */
  object weakFairness extends TlaTempOper {
    override val name: String = "WF"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (4, 15)
  }

  /**
   * The strong fairness operator SF_x(A). The argument order is: (x, A)
   */
  object strongFairness extends TlaTempOper {
    override val name: String = "SF"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (4, 15)
  }

  /** The temporal existential quantification (hiding) operator */
  object EE extends TlaTempOper {
    override val name: String = "\\EE"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (0, 0) // Sec 15.2.1, Undelimited Constructs
  }

  /** The temporal universal quantification operator */
  object AA extends TlaTempOper {
    override val name: String = "\\AA"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (0, 0) // Sec 15.2.1, Undelimited Constructs
  }
}
