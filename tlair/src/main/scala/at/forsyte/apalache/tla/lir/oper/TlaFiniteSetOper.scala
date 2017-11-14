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
  val isFiniteSet = new TlaFiniteSetOper {
    override val arity = FixedArity(1)
    override val name = "IsFiniteSet"
  }

  /**
    * The operator that returns the cardinality of a finite set.
    */
  val cardinality = new TlaFiniteSetOper {
    override val arity = FixedArity(1)
    override val name = "Cardinality"
  }

}
