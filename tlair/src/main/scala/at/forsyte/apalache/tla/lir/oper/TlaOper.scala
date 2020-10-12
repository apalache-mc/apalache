package at.forsyte.apalache.tla.lir.oper

import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.values.TlaStr

/** An abstract operator */
trait TlaOper extends Serializable {
  def name: String

  def interpretation: Interpretation.Value

  /* the number of arguments the operator is allowed to have */
  def arity: OperArity

  /**
    * Operator precedence. See: Lamport. Specifying Systems, 2004, p. 271, Table 6.
    * @return the range that defines operator precedence [a, b].
    */
  def precedence: (Int, Int)

  /**
    * Is the operator allowed to have that many arguments?
    * @param a the number of arguments
    * @return true, if this number of arguments is allowed.
    */
  def isCorrectArity(a: Int): Boolean = arity.cond(a)

  /**
    * Do the operator arguments satisfy the operator invariant?
    * For instance, some operators only allow name expressions in certain positions.
    *
    * @param args operator arguments
    * @return true, if the invariant is satisfied
    */
  def permitsArgs(args: Seq[TlaEx]): Boolean = { true }
}

object TlaOper {
  /** Equality of two TLA+ objects */
  object eq extends TlaOper {
    val name = "="
    val interpretation: Interpretation.Value = Interpretation.Predefined
    val arity = FixedArity(2)
    override val precedence: (Int, Int) = (5, 5)
  }

  /** Inequality of two TLA+ objects */
  object ne extends TlaOper {
    val name = "/="
    val interpretation: Interpretation.Value = Interpretation.Predefined
    val arity = FixedArity(2)
    override val precedence: (Int, Int) = (5, 5)
  }

  /**
    * Operator application by name, e.g, OperEx(apply, f, x, y) calls f(x, y).
    *
    * This is an operator that you will not find in TLA+ code.
    * The only case where this operator is used are the level 2 user-defined operators,
    * that is, when one defines A(f(_), i) == f(i), the A's body is defined as
    * OperEx(apply, NameEx("f"), NameEx("i")).
    *
    * @see TestSanyImporter.test("level-2 operators")
    */
  object apply extends TlaOper {
    override def arity: OperArity = AnyPositiveArity()

    override def interpretation: Interpretation.Value = Interpretation.Predefined
    override val name: String = "_()"
    override val precedence: (Int, Int) = (16, 16)
  }

  /**
    * The CHOOSE operator: CHOOSE x \in S: p
    */
  object chooseBounded extends TlaOper {
    // TODO: move this operator to TlaBoolOper? (Igor)
    /* the number of arguments the operator has */
    override val name: String = "CHOOSE3"

    override def arity: OperArity = FixedArity(3)

    override def interpretation: Interpretation.Value = Interpretation.Predefined

    override val precedence: (Int, Int) = (0, 0) // see Section 15.2.1 in Lamport's book
  }

  /**
    * The CHOOSE operator: CHOOSE x : p
    */
  object chooseUnbounded extends TlaOper {
    // TODO: move this operator to TlaBoolOper? (Igor)
    /* the number of arguments the operator has */
    override val name: String = "CHOOSE2"

    override def arity: OperArity = FixedArity(2)

    override def interpretation: Interpretation.Value = Interpretation.Predefined

    override val precedence: (Int, Int) = (0, 0) // see Section 15.2.1 in Lamport's book
  }

  /** The CHOOSE idiom: CHOOSE x : x \notin S */
  object chooseIdiom extends TlaOper {
    // TODO: move this operator to TlaBoolOper? (Igor)
    override val name: String = "CHOOSEI"

    override def arity: OperArity = FixedArity(1)

    override def interpretation: Interpretation.Value = Interpretation.Predefined

    override val precedence: (Int, Int) = (0, 0) // Section 15.2.1
  }

  /**
    * <p>An operator that decorates an expression with a label, e.g., l3(a, b) :: ex.
    * The order of the arguments is as follows: (1) the decorated expression, e.g., ex,
    * (2) the label, e.g., ValEx(TlaStr("l3")), and (3 to k) the label arguments,
    * which must be strings, e.g., ValEx(TlaStr("a")) and ValEx(TlaStr("b")).</p>
    *
    * <p>To get more info about labels, see
    * <a href="http://research.microsoft.com/en-us/um/people/lamport/tla/tla2-guide.pdf">TLA+2 Preliminary Guide</a>.</p>
    *
    * <p>Technically, a label is not an operator in TLA+, but a special form of an expression.
    * As the labels are rarely used, we have decided to introduce a new operator instead of
    * extending TlaEx with a new case class (it would have been annoying to take care of LabelEx
    * in the pattern-matching code).</p>
    */
  object label extends TlaControlOper {
    override val name: String = "LABEL"

    override def arity: OperArity = MinimalArity(2)

    override val interpretation: Interpretation.Value = Interpretation.Predefined

    override val precedence: (Int, Int) = (16, 16) // similar to function application

    /**
      * Do the operator arguments satisfy the operator invariant?
      * For instance, some operators only allow name expressions in certain positions.
      *
      * @param args operator arguments
      * @return true, if the invariant is satisfied
      */
    override def permitsArgs(args: Seq[TlaEx]): Boolean = {
      val isNameEx: PartialFunction[TlaEx, Boolean] = { case ValEx(TlaStr(_)) => true }
      args.tail.forall(isNameEx.isDefinedAt)
    }
  }

}
