package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._

/**
 * Action operators.
 */
package object actions {
  abstract class TlaActionOper extends TlaOper {
    override def level: Level.Value = Level.Action
    override def interpretation: Interpretation.Value = Interpretation.Predefined
  }
  
  object TlaActionOper {
    /**
     * The prime operator. By the TLA+ restrictions, we cannot apply it twice, e.g., (x')' is illegal.
     */
    val TlaPrimeOper = new TlaActionOper {
      override def name: String = "'"
      override def arity: OperArity = FixedArity(1)
    }

    /**
     * The operator that executes an action or keeps the variable values.
     */
    val TlaStutterOper = new TlaActionOper {
      override def name: String = "[A]_e"
      override def arity: OperArity = FixedArity(2)
    }

    /**
     * The operator that executes an action and enforces the values to change.
     */
    val TlaNoStutterOper = new TlaActionOper {
      override def name: String = "<A>_e"
      override def arity: OperArity = FixedArity(2)
    }

    /**
     * The ENABLED operator.
     */
    val TlaEnabledOper = new TlaActionOper {
      override def name: String = "ENABLED"
      override def arity: OperArity = FixedArity(1)
    }

    /**
     * The operator that executes an action or keeps the variable values.
     */
    val TlaUnchangedOper = new TlaActionOper {
      override def name: String = "UNCHANGED"
      override def arity: OperArity = FixedArity(1)
    }

    /**
     * The sequential composition.
     */
    val TlaCompisitionOper = new TlaActionOper {
      override def name: String = "\\cdot"
      override def arity: OperArity = FixedArity(1)
    }
  }
}
