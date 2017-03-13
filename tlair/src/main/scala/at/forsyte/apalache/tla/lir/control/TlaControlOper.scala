package at.forsyte.apalache.tla.lir.control

import at.forsyte.apalache.tla.lir.oper._

/**
 * Control-flow operators
 */
abstract class TlaControlOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.Predefined
}

object TlaControlOper {
  /**
    * A case operator without the OTHER option. The arguments are always an even-length list
    * of the following structure: guard_1, eff_1, guard_2, eff_2, ..., guard_k, eff_k.
    */
  val caseNoOther = new TlaControlOper {
    override val name: String = "CASE"
    override val arity: OperArity = AnyEvenArity()
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }

  /**
    * A case operator with the OTHER option. The arguments are always an odd-length list
    * of the following structure: eff_OTHER, guard_1, eff_1, guard_2, eff_2, ..., guard_k, eff_k.
    * That is, the first expression is the expression matching the OTHER option.
    * The rationale is that by using args.tail, one obtains a list similar to the caseOper.
    */
  val caseWithOther = new TlaControlOper {
    override val name: String = "CASE-OTHER"
    override val arity: OperArity = AnyOddArity()
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }

  /**
    * The "IF A THEN B ELSE C" operator. The arguments have the following structure: A, B, C.
    */
  val ifThenElse = new TlaControlOper {
    override val name: String = "IF-THEN-ELSE"
    override val arity: OperArity = FixedArity(3)
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }

  /**
    * The LET x_1 = e_1, ..., x_k = e_k in A. The arguments are always an ood-length list
    * of the following structure: A, x_1, e_1, ..., x_k, e_k.
    * The rationale is that (1) args.head gives us the body, and (2) args.tail gives us
    * an interleaved list of bound variables and bound expressions.
    */
  val letIn = new TlaControlOper {
    override val name: String = "LET-IN"
    override val arity: OperArity = AnyOddArity()
    override val interpretation: Interpretation.Value = Interpretation.Predefined
  }
}


