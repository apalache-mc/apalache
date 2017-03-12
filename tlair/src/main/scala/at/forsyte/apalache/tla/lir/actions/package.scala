package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._

/**
  * Action operators.
  */
package object actions {

  abstract class TlaActionOper extends TlaOper {
    override def interpretation: Interpretation.Value = Interpretation.Predefined
  }

  object TlaActionOper {
    /**
      * The prime operator. By the TLA+ restrictions, we cannot apply it twice, e.g., (x')' is illegal.
      */
    val prime = new TlaActionOper {
      override def name: String = "'"

      override def arity: OperArity = FixedArity(1)
    }

    /**
      * The operator that executes an action or keeps the variable values.
      */
    val stutter = new TlaActionOper {
      override def name: String = "[A]_e"

      override def arity: OperArity = FixedArity(2)
    }

    /**
      * The operator that executes an action and enforces the values to change.
      */
    val nostutter = new TlaActionOper {
      override def name: String = "<A>_e"

      override def arity: OperArity = FixedArity(2)
    }

    /**
      * The ENABLED operator.
      */
    val enabled = new TlaActionOper {
      override def name: String = "ENABLED"

      override def arity: OperArity = FixedArity(1)
    }

    /**
      * The operator that executes an action or keeps the variable values.
      */
    val unchanged = new TlaActionOper {
      override def name: String = "UNCHANGED"

      override def arity: OperArity = FixedArity(1)
    }

    /**
      * The sequential composition of operators.
      *
      * Jure@17.11.16: Arity 2?
      * Igor@12.03.17: Arity 2. Fixed.
      */
    val composition = new TlaActionOper {
      override def name: String = "\\cdot"

      override def arity: OperArity = FixedArity(2)
    }
  }

}
