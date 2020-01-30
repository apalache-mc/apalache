package at.forsyte.apalache.tla.lir.oper

/**
  * The operators defined in the BMC module. This module give the users a facility to provide hints.
  * To use this module, the user would have to copy the module somewhere. As our tool is not widely used,
  * we just hijack some operators during the import stage, e.g., <:
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
    override def name: String = "BMC!<-"
    override def arity: OperArity = FixedArity(2)
    override val precedence: (Int, Int) = (100, 100)
  }

  /**
    * Skolemization hint. In an expression Skolem(\E x \in S: e), the existential may be skolemized, that is, translated
    * into a constant.
    */
  val skolemExists: BmcOper = new BmcOper {
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
}


