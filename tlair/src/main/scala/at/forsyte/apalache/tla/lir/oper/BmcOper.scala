package at.forsyte.apalache.tla.lir.oper

/**
 * The operators defined in the BMC module. This module give the users a facility to provide hints.
  *
  * @author konnov
 */
abstract class BmcOper extends TlaOper {
  override def interpretation: Interpretation.Value = Interpretation.StandardLib
}

object BmcOper {
  /**
    * Print(out, val) from TLC.
    */
  val withType: BmcOper = new BmcOper {
    override def name: String = "BMC!WithType"
    override def arity: OperArity = FixedArity(2)
  }
}


