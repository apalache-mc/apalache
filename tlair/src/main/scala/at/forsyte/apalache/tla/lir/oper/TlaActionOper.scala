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
    override val name: String = "'"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (15, 15)
  }

  /**
   * The operator that executes an action or keeps the variable values.
   */
  object stutter extends TlaActionOper {
    override val name: String = "[A]_e"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (4, 15)
  }

  /**
   * The operator that executes an action and enforces the values to change.
   */
  object nostutter extends TlaActionOper {
    override val name: String = "<A>_e"

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
   * The sequential composition of operators.
   *
   * Jure@17.11.16: Arity 2?
   * Igor@12.03.17: Arity 2. Fixed.
   */
  object composition extends TlaActionOper {
    override val name: String = "\\cdot"
    override def arity: OperArity = FixedArity(2)
    override def precedence: (Int, Int) = (13, 13)
  }
}
