package at.forsyte.apalache.tla.lir

/**
  * TLA+ operators.
  */
package oper {

  import at.forsyte.apalache.tla.lir.values.TlaStr

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

  class OperArity(private val m_cond: Int => Boolean) {
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

  /** An abstract operator */
  trait TlaOper {
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
    val eq: TlaOper = new TlaOper {
      val name = "="
      val interpretation: Interpretation.Value = Interpretation.Predefined
      val arity = FixedArity(2)
      override val precedence: (Int, Int) = (5, 5)
    }

    /** Inequality of two TLA+ objects */
    val ne: TlaOper = new TlaOper {
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
    val apply: TlaOper = new TlaOper {
      override def arity: OperArity = AnyPositiveArity()

      override def interpretation: Interpretation.Value = Interpretation.Predefined
      override val name: String = "_()"
      override val precedence: (Int, Int) = (16, 16)
    }

    /**
      * The CHOOSE operator: CHOOSE x \in S: p
      */
    val chooseBounded: TlaOper = new TlaOper {
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
    val chooseUnbounded: TlaOper = new TlaOper {
      // TODO: move this operator to TlaBoolOper? (Igor)
      /* the number of arguments the operator has */
      override val name: String = "CHOOSE2"

      override def arity: OperArity = FixedArity(2)

      override def interpretation: Interpretation.Value = Interpretation.Predefined

      override val precedence: (Int, Int) = (0, 0) // see Section 15.2.1 in Lamport's book
    }

    /** The CHOOSE idiom: CHOOSE x : x \notin S */
    val chooseIdiom: TlaOper = new TlaOper {
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
    val label: TlaOper = new TlaControlOper {
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

}
