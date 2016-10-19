package at.forsyte.apalache.tla.lir

/**
 * Operators.
 */
package oper {

  /**
     The levels of the operators: State (reasons about current state), Action (reasons about a pair of states),
     and Temporal (reasons about executions).
    */
  object Level extends Enumeration {
    val State, Transition, Temporal = Value
  }

  /**
     Interpretation shows how standard an operator is: Predefined (fixed interpretation),
     StandardLib (many standard interpretations), User (user-defined).
    */
  object Interpretation extends Enumeration {
    /** this operator has a fixed and the only interpretation in TLA+, e.g., \cup, \cap. */
    val Predefined = Value
    /** this operator has some interpretation defined in a standard module, e.g., Integers!+, Real!+. */
    val StandardLib = Value
    /** this operator is defined by the user and unknown to TLA+ */
    val User = Value
  }

  abstract class OperArity
  case class AnyArity() extends OperArity
  case class FixedArity(n: Int) extends OperArity

  /** An abstract operator */
  abstract class TlaOper {
    def name: String
    def level: Level.Value
    def interpretation: Interpretation.Value
    /* the number of arguments the operator has */
    def arity: OperArity

    def isCorrectArity(a: Int): Boolean = {
      arity match {
        case AnyArity() => a >= 0
        case FixedArity(n) => a == n
      }
    }
  }

  object TlaOper {
    /** Equality of two TLA+ objects */
    val eq = new TlaOper {
      val name = "="
      val level = Level.State
      val interpretation = Interpretation.Predefined
      val arity = FixedArity(2)
    }

    /** Inequality of two TLA+ objects */
    val ne = new TlaOper {
      val name = "/="
      val level = Level.State
      val interpretation = Interpretation.Predefined
      val arity = FixedArity(2)
    }
  }

}
