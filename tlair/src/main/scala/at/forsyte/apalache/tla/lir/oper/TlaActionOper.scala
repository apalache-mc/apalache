package at.forsyte.apalache.tla.lir.oper

/**
 * An action operator.
 */
abstract class TlaActionOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaActionOper {

  /**
   * The prime operator. By the TLA+ restrictions, we cannot apply it twice, e.g., (x')' is illegal.
   */
  object prime extends TlaActionOper {
    override val name: String = "PRIME"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (15, 15)
  }

  /**
   * The operator that executes an action or keeps the variable values. It has the form `[A]_e`.
   */
  object stutter extends TlaActionOper {
    override val name: String = "STUTTER"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (4, 15)
  }

  /**
   * The operator that executes an action and enforces the values to change. It has the form `<A>_e`.
   */
  object nostutter extends TlaActionOper {
    override val name: String = "NO_STUTTER"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (4, 15)
  }

  /**
   * The ENABLED operator.
   */
  object enabled extends TlaActionOper {
    override val name: String = "ENABLED"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (4, 15)
  }

  /**
   * The operator that executes an action or keeps the variable values.
   */
  object unchanged extends TlaActionOper {
    override val name: String = "UNCHANGED"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (4, 15)
  }

  /**
   * The sequential composition of operators, which usually has the name `\cdot`.
   */
  object composition extends TlaActionOper {
    override val name: String = "COMPOSE"
    override def arity: OperArity = FixedArity(2)
    override def precedence: (Int, Int) = (13, 13)
  }
}
