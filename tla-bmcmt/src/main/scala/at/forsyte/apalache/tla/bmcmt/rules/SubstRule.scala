package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.NameEx

/**
  * Implements the rules SE-SUBST1
   */
class SubstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(state: SymbState): Boolean = {
    state.rex match {
      case TlaRex(NameEx(x)) =>
        state.binding.contains(x)

      case _ => false
    }
  }

  override def apply(state: SymbState, dir: SymbStateRewriter.SearchDirection): SymbState = {
    state.rex match {
      case TlaRex(NameEx(x)) =>
        val cell = state.binding.apply(x)
        state.setRex(TlaRex(NameEx(cell.toString)))

      case _ =>
        throw new RewriterException("SubstRule is not applicable")
    }
  }
}
