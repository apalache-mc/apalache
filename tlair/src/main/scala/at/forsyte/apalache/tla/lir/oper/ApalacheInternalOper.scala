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
   * The distinct operator that is equivalent to (distinct ...) in SMT-LIB. Formally, BMC!Distinct(x_1, ..., x_n) is
   * equivalent to \A i, j \in 1..n: i /= j => x_i /= x_j.
   *
   * XXX: there seems to be no way of defining a user-defined variadic operator in Apalache.tla.
   */
  object distinct extends ApalacheInternalOper {
    override def name: String = "Apalache!Distinct"

    override def arity: OperArity = AnyArity()

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * This operator returns the capacity of a given sequence, that is, a static upper bound on its length.
   */
  object apalacheSeqCapacity extends ApalacheInternalOper {
    override def name: String = "ApalacheInternal!__ApalacheSeqCapacity"

    override def arity: OperArity = FixedArity(1)

    override val precedence: (Int, Int) = (100, 100)
  }

  /**
   * The selectInSet operator is a variant of TlaSetOper.in. It signals that set membership should be checked.
   */
  object selectInSet extends ApalacheInternalOper {
    override def name: String = "Apalache!SelectInSet"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The selectInFun operator returns the result of applying a function to a given element.
   */
  object selectInFun extends ApalacheInternalOper {
    override def name: String = "Apalache!SelectInFun"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The storeInSet operator is a variant of TlaSetOper.in when handling sets. It signals set membership. It is also
   * used to update functions, in which case the updated value is provided as an additional argument.
   */
  object storeInSet extends ApalacheInternalOper {
    override def name: String = "Apalache!StoreInSet"

    override def arity: OperArity = FixedArity(2) || FixedArity(3)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The storeNotInSet operator is a variant of storeInSet. It signals that the negation of set membership should be
   * enforced.
   */
  object storeNotInSet extends ApalacheInternalOper {
    override def name: String = "Apalache!storeNotInSet"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The storeNotInFun operator is a variant of storeNotInSet. It signals that a function, which is undefined for a
   * given argument, remains undefined for that argument.
   */
  object storeNotInFun extends ApalacheInternalOper {
    override def name: String = "Apalache!storeNotInFun"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The smtMap operator applies an SMT map using conjunction to two cells encoded as SMT arrays. Its current use is to
   * encoded set intersection, when handling TLA+ filters, and set union.
   */
  case class smtMap(mapOper: TlaOper) extends ApalacheInternalOper {
    override def name: String = s"Apalache!SmtMap_${mapOper.name}"

    override def arity: OperArity = FixedArity(2)

    override def precedence: (Int, Int) = (5, 5)
  }

  /**
   * The unconstrainArray operator increases the SSA index of a cell encoded as an SMT array.
   */
  object unconstrainArray extends ApalacheInternalOper {
    override def name: String = "Apalache!UnconstrainArray"

    override def arity: OperArity = FixedArity(1)

    override def precedence: (Int, Int) = (5, 5)
  }
}
