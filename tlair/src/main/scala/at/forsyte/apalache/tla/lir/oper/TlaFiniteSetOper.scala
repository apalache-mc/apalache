package at.forsyte.apalache.tla.lir.oper

/**
 * The operators defined in the FiniteSets module.
  *
  * @author konnov
 */
abstract class TlaFiniteSetOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object TlaFiniteSetOper {
  /**
    * The operator that checks, whether a set is finite.
    */
  object isFiniteSet extends TlaFiniteSetOper {
    override val arity = FixedArity(1)
    override val name = "IsFiniteSet"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

  /**
    * The operator that returns the cardinality of a finite set.
    */
  object cardinality extends TlaFiniteSetOper {
    override val arity = FixedArity(1)
    override val name = "Cardinality"
    override val precedence: (Int, Int) = (16, 16) // as the function application
  }

}
