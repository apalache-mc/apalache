package at.forsyte.apalache.tla.lir.oper

/**
  * An abstract class of arithmetic operators.
  *
  * @author jkukovec
  */

abstract class TlaArithOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
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
    * An n-ary sum, that is, Sum(x_1, ..., x_n) = x_1 + ... + x_n.
    */
  val sum = new TlaArithOper {
    override val arity = AnyArity()
    // Empty sum = 0
    override val name = "SUM"
  }

  /**
    * A binary addition.
    */
  val plus = new TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "(+)"
  }

  /**
    * A unary minus. Note that Naturals do not have unary minus.
    */
  val uminus = new TlaArithOper {
    override val arity = FixedArity(1)
    override val name = "-."
  }

  /**
    * A binary minus.
    */
  val minus = new TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "(-)"
  }

  /**
    * An n-ary product of the arguments, that is, Prod(x_1, ..., x_n) = x_1 * ... * x_n.
    */
  val prod = new TlaArithOper {
    override def arity = AnyArity()

    // empty prod = 1
    override val name = "PROD"
  }

  /**
    * A multiplication.
    */
  val mult = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(*)"
  }

  /**
    * Integer division.
    */
  val div = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(\\div)"
  }

  /**
    * Remainder of an integer division.
    */
  val mod = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(%)"
  }

  /**
    * Real division.
    */
  val realDiv = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(/)"
  }

  /**
    * Exponent, i.e., x^y gives us x multiplied by itself (y-1) times.
    **/
  val exp = new TlaArithOper {
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(^)"
  }

  /**
    * An integer/natural range, that is, a..b = {a,...,b}
    */
  val dotdot = new TlaArithOper {
    override val arity = FixedArity(2)
    override val name = "_.._"
  }

  /**
    * Less than.
    */
  val lt = new TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(<)"
  }

  /**
    * Greater than.
    */
  val gt = new TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(>)"
  }

  /**
    * Less than or equals.
    */
  val le = new TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(<=)"
  }

  /**
    * Greater than or equals.
    */
  val ge = new TlaArithOper {
    /* the number of arguments the operator has */
    override def arity: OperArity = FixedArity(2)

    override val name: String = "(>=)"
  }

}
