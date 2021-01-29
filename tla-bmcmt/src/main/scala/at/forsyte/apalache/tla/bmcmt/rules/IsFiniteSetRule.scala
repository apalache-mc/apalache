package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFiniteSetOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}


/**
  * Implements the IsFiniteSet operator. It is trivial in our case.
  *
  * @author Igor Konnov
  */
class IsFiniteSetRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaFiniteSetOper.isFiniteSet, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFiniteSetOper.isFiniteSet, setEx) =>
        // All our sets are finite. Non-sets should be rejected by the type checker. So, just return true.
        state.setRex(state.arena.cellTrue())

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
