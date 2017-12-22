package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.NameEx

/**
  * Implements the rule SE-SUBST1.
  *
  * @author Igor Konnov
   */
class SubstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case NameEx(x) =>
        state.binding.contains(x)

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(x) =>
        val cell = state.binding.apply(x)
        state.setRex(NameEx(cell.toString))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
