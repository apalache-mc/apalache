package at.forsyte.apalache.tla.lir

/**
  * TLA+ operators.
  */
package oper {

  import at.forsyte.apalache.tla.lir.control.TlaControlOper

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

  class OperArity(cond: Int => Boolean) {
    val m_cond: Int => Boolean = n => if (n < 0) false else cond(n)
  }

  sealed case class AnyArity() extends OperArity(_ => true)

  sealed case class FixedArity(n: Int) extends OperArity(_ == n)

  sealed case class AnyOddArity() extends OperArity(_ % 2 == 1)

  sealed case class AnyEvenArity() extends OperArity(_ % 2 == 0)

  sealed case class AnyPositiveArity() extends OperArity(_ > 0)

  /** An abstract operator */
  trait TlaOper {
    def name: String

    def interpretation: Interpretation.Value

    /* the number of arguments the operator has */
    def arity: OperArity

    def isCorrectArity(a: Int): Boolean = arity.m_cond(a)
  }

  object TlaOper {
    /** Equality of two TLA+ objects */
    val eq: TlaOper = new TlaOper {
      val name = "="
      val interpretation: Interpretation.Value = Interpretation.Predefined
      val arity = FixedArity(2)
    }

    /** Inequality of two TLA+ objects */
    val ne: TlaOper = new TlaOper {
      val name = "/="
      val interpretation: Interpretation.Value = Interpretation.Predefined
      val arity = FixedArity(2)
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
    }

    /** The CHOOSE operator: CHOOSE x \in S: p */
    val chooseBounded: TlaOper = new TlaOper {
      /* the number of arguments the operator has */
      override val name: String = "CHOOSE3"

      override def arity: OperArity = FixedArity(3)

      override def interpretation: Interpretation.Value = Interpretation.Predefined
    }

    /** The CHOOSE operator: CHOOSE x : p */
    val chooseUnbounded: TlaOper = new TlaOper {
      /* the number of arguments the operator has */
      override val name: String = "CHOOSE2"

      override def arity: OperArity = FixedArity(2)

      override def interpretation: Interpretation.Value = Interpretation.Predefined
    }

    /** The CHOOSE idiom: CHOOSE x : x \notin S */
    val chooseIdiom: TlaOper = new TlaOper {
      override val name : String = "CHOOSEI"

      override def arity : OperArity = FixedArity(1)

      override def interpretation : Interpretation.Value = Interpretation.Predefined
    }

    /**
      * An operator that decorates an expression with a label, e.g., l3(a, b) :: ex.
      * The order of the arguments is as follows: (1) the decorated expression, e.g., ex,
      * (2) the label name, e.g., NameEx("l3"), and (3 to k) the label arguments, e.g.,
      * NameEx("a") and NameEx("b").
      *
      * Technically, a label is not an operator in TLA+, but a special form of an expression.
      * As the labels are rarely used, we have decided to introduce a new operator instead of
      * extending TlaEx with a new case class (it would have been annoying to take care of LabelEx
      * in the pattern-matching code).
      */
    val label = new TlaControlOper {
      override val name: String = "LABEL"
      override def arity: OperArity = new OperArity(_ >= 2)
      override val interpretation: Interpretation.Value = Interpretation.Predefined
    }

  }
}
