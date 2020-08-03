package at.forsyte.apalache.tla.lir.oper

/**
  * The operators defined in the module Apalache.tla. This module gives the users a facility to provide hints.
  * The "Apalache" module is automatically looked up when Apalache is running.
  *
  * TODO: rename this class to ApalacheOper, once ik/multicore is merged into unstable.
  *
  * @author konnov
 */
abstract class BmcOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object BmcOper {
  /**
    * A type annotation of an expression with another expression that encodes a type.
    */
  val withType: BmcOper = new BmcOper {
    override def name: String = "BMC!<:"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (100, 100)
  }

  /**
    * An operator x <- e that is interpreted as an assignment of e to x (the variable can have a prime too).
    */
  val assign: BmcOper = new BmcOper {
    override def name: String = "BMC!:="
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (100, 100)
  }

  /**
    * Skolemization hint. In an expression Skolem(\E x \in S: e), the existential may be skolemized, that is, translated
    * into a constant.
    */
  val skolem: BmcOper = new BmcOper {
    override def name: String = "BMC!Skolem"
    override def arity: OperArity = FixedArity(1)
    override def precedence: (Int, Int) = (100, 100)
  }

  /**
    * An expansion hint that can be applied to SUBSET S or [S -> T]. This hint orders the rewriter
    * to expand the underlying expression into a finite set. Since, such an expansion results in an exponential
    * blow up, this should be done carefully (and avoided as much as possible).
    */
  val expand: BmcOper = new BmcOper {
    override def name: String = "BMC!Expand"
    override def arity: OperArity = FixedArity(1)
    override def precedence: (Int, Int) = (100, 100)
  }

  /**
    * An optimization hint for a cardinality constraint like Cardinality(S) >= k, where k is a constant.
    * Similar to BMC!Skolem, this optimization has to be applied carefully, as it is not sound, when the cardinality
    * test is located under negation.
    */
  val constCard: BmcOper = new BmcOper {
    override def name: String = "BMC!ConstCardinality"
    override def arity: OperArity = FixedArity(1)
    override def precedence: (Int, Int) = (100, 100)
  }

  /**
    * The distinct operator that is equivalent to (distinct ...) in SMT-LIB.
    * Formally, BMC!Distinct(x_1, ..., x_n) is equivalent to \A i, j \in 1..n: i /= j => x_i /= x_j.
    *
    * XXX: there seems to be no way of defining a user-defined variadic operator in Apalache.tla.
    */
  val distinct: BmcOper = new BmcOper {
    override def name: String = "BMC!Distinct"
    override def arity: OperArity = AnyArity()
    override def precedence: (Int, Int) = (5, 5)
  }
}

