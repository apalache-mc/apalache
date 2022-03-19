package at.forsyte.apalache.tla.lir.oper

/**
 * The operators defined in the module `__apalache_internals.tla`. The operators in this module are designed for the
 * Apalache code and its internal TLA+ definitions. The users should not use these operators.
 *
 * @author
 *   Igor Konnov
 */
abstract class ApalacheInternalOper extends ApalacheOper

object ApalacheInternalOper {

  /**
   * This operator receives an error message (a string literal), which should be printed if this operator reaches the
   * model checker.
   */
  object notSupportedByModelChecker extends ApalacheInternalOper {
    override def name: String = "ApalacheInternal!__NotSupportedByModelChecker"

    override def arity: OperArity = FixedArity(1)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * This operator returns the capacity of a given sequence, that is, a static upper bound on its length.
   */
  object apalacheSeqCapacity extends ApalacheInternalOper {
    override def name: String = "ApalacheInternal!__ApalacheSeqCapacity"

    override def arity: OperArity = FixedArity(1)

    override val precedence: (Int, Int) = (100, 100)
  }

}
