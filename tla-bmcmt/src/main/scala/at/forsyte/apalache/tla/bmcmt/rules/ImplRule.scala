package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper

/**
  * Implements an implication A => B by rewriting it to ~A \/ B.
  *
  * @author Igor Konnov
  */
class ImplRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val substRule = new SubstRule(rewriter)
  private val simplifier = new ConstSimplifier()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaBoolOper.implies, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaBoolOper.implies, left, right) =>
        state.setRex(simplifier.simplify(tla.or(tla.not(left), right)))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
