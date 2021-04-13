package at.forsyte.apalache.tla.lir.oper

import at.forsyte.apalache.tla.lir.TlaOperDecl

/**
 * A control-flow operator.
 */
abstract class TlaControlOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaControlOper {

  /**
   * A case operator without the OTHER option. The arguments are always an even-length list
   * of the following structure: guard_1, eff_1, guard_2, eff_2, ..., guard_k, eff_k.
   */
  object caseNoOther extends TlaControlOper {
    override val name: String = "CASE"
    override val arity: OperArity = MinimalArity(2) && AnyEvenArity() //new OperArity( k => k >= 2 && k % 2 == 0 )
    override val interpretation: Interpretation.Value = Interpretation.Predefined
    override val precedence: (Int, Int) = (0, 0)
  }

  /**
   * A case operator with the OTHER option. The arguments are always an odd-length list
   * of the following structure: eff_OTHER, guard_1, eff_1, guard_2, eff_2, ..., guard_k, eff_k.
   * That is, the first expression is the expression matching the OTHER option.
   * The rationale is that by using args.tail, one obtains a list similar to the caseOper.
   */
  object caseWithOther extends TlaControlOper {
    override val name: String = "CASE_OTHER"
    override val arity: OperArity = MinimalArity(3) && AnyOddArity() //new OperArity( k => k >= 3 && k % 2 == 1 )
    override val interpretation: Interpretation.Value = Interpretation.Predefined
    override val precedence: (Int, Int) = (0, 0)
  }

  /**
   * The "IF A THEN B ELSE C" operator. The arguments have the following structure: A, B, C.
   */
  object ifThenElse extends TlaControlOper {
    override val name: String = "IF_THEN_ELSE"
    override val arity: OperArity = FixedArity(3)
    override val interpretation: Interpretation.Value = Interpretation.Predefined
    override val precedence: (Int, Int) = (0, 0)
  }
}
