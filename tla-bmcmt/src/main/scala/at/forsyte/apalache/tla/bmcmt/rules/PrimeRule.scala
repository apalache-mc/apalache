package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.actions.TlaActionOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Rename x' to NameEx("x'"). We only consider the case when prime is applied to a variable.
  *
  * @author Igor Konnov
  */
class PrimeRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaActionOper.prime, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaActionOper.prime, NameEx(name)) =>
        state.setRex(NameEx(name + "'"))

      case _ =>
        throw new RewriterException("Prime operator is only implemented for variables")
    }
  }
}
