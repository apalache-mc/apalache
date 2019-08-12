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
}


