package at.forsyte.apalache.tla.lir

import at.forsyte.apalache.tla.lir.oper._

/**
 * Temporal operators.
 */
package object temporal {
  abstract class TemporalOper extends TlaOper {
    override def level: Level.Value = Level.Temporal
    override def interpretation: Interpretation.Value = Interpretation.Predefined
  }

  object TemporalOper {
    /** The LTL box operator */
    val box = new TemporalOper {
      override def name: String = "[]"
      override def arity: OperArity = FixedArity(1)
    }

    /** The LTL diamond operator */
    val diamond = new TemporalOper {
      override def name: String = "<>"
      override def arity: OperArity = FixedArity(1)
    }

    /** The leads-to operator */
    val leadsTo = new TemporalOper {
      override def name: String = "~>"
      override def arity: OperArity = FixedArity(2)
    }

    /** The 'guarantees' operator */
    val guarantees = new TemporalOper {
      override def name: String = "-+->"
      override def arity: OperArity = FixedArity(2)
    }

    /** The weak fairness operator */
    val weakFairness = new TemporalOper {
      override def name: String = "WF"
      override def arity: OperArity = FixedArity(2)
    }

    /** The strong fairness operator */
    val strongFairness = new TemporalOper {
      override def name: String = "SF"
      override def arity: OperArity = FixedArity(2)
    }

    /** The temporal existential quantification (hiding) operator */
    val EE = new TemporalOper {
      override def name: String = "\\EE"
      override def arity: OperArity = FixedArity(2)
    }

    /** The temporal universal quantification operator */
    val AA = new TemporalOper {
      override def name: String = "\\AA"
      override def arity: OperArity = FixedArity(2)
    }
  }
}
