package at.forsyte.apalache.tla.lir.oper

/**
 * An abstract class of arithmetic operators.
 *
 * @author jkukovec
 */

abstract class TlaArithOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

/**
 * <p>Arithmetic operators in TLA+ (as defined in Naturals, Integers, and Reals).
 * Note that modules inherit operator definitions. In other words,
 * Reals inherits definitions of + and - from Integers, which inherit definitions from Naturals.
 * Thus, though these operators are semantically different, these operators are introduced using
 * the same definition in TLA+ tools. We also instantiate each operator only once.</p>
 *
 * <p>Alternatively, we could have introduced multiple copies of each operator (for Naturals, Integers, and Reals)
 * and use the most general operator, e.g., using addition on reals, when a module extends Reals.
 * However, this would not give us precise type information when one mixes integer and real arithmetic.
 * Consequently, we use just one copy per operator and hope that type analysis would be able to infer tighter types.</p>
 *
 * @author jkukovec, konnov
 */
object TlaArithOper {

  /**
   * A binary addition.
   */
  object plus extends TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "(+)"
    override val precedence: (Int, Int) = (10, 10)
  }

  /**
   * A unary minus. Note that Naturals do not have unary minus.
   */
  object uminus extends TlaArithOper {
    override val arity = FixedArity(1)
    override val name = "-."
    override val precedence: (Int, Int) = (12, 12)
  }

  /**
   * A binary minus.
   */
  object minus extends TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "(-)"
    override val precedence: (Int, Int) = (11, 11)
  }

  /**
   * A multiplication.
   */
  object mult extends TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(*)"
    override val precedence: (Int, Int) = (13, 13)
  }

  /**
   * Integer division.
   */
  object div extends TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(\\div)"
    override val precedence: (Int, Int) = (13, 13)
  }

  /**
   * Remainder of an integer division.
   */
  object mod extends TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(%)"
    override val precedence: (Int, Int) = (10, 11)
  }

  /**
   * Real division.
   */
  object realDiv extends TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(/)"
    override val precedence: (Int, Int) = (13, 13)
  }

  /**
   * Exponent, i.e., x^y gives us x multiplied by itself (y-1) times.
   */
  object exp extends TlaArithOper {
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(^)"
    override val precedence: (Int, Int) = (14, 14)
  }

  /**
   * An integer/natural range, that is, a..b = {a,...,b}
   */
  object dotdot extends TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "_.._"
    override val precedence: (Int, Int) = (9, 9)
  }

  /**
   * Less than.
   */
  object lt extends TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(<)"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
   * Greater than.
   */
  object gt extends TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(>)"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
   * Less than or equals.
   */
  object le extends TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(<=)"
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
   * Greater than or equals.
   */
  object ge extends TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)
    override val name: String = "(>=)"
    override val precedence: (Int, Int) = (5, 5)
  }
}
