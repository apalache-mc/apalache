package at.forsyte.apalache.tla.lir.control

import at.forsyte.apalache.tla.lir.oper._

/**
 * Control-flow operators
 */
abstract class TlaControlOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaControlOper {
  val caseOper = new TlaControlOper {
    override val name: String = "CASE"
    override val arity: OperArity = AnyEvenArity()
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }

  val caseWithOther = new TlaControlOper {
    override val name: String = "CASE-OTHER"
    override val arity: OperArity = AnyOddArity()
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }

  val ifThenElse = new TlaControlOper {
    override val name: String = "IF-THEN-ELSE"
    override val arity: OperArity = FixedArity(3)
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }

  val letIn = new TlaControlOper {
    override val name: String = "LET-IN"
    override val arity: OperArity = AnyOddArity()
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }
}


