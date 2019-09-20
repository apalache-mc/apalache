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
        // make sure that x is not an SMT constant, but a variable name
        !CellTheory().hasConst(x) && !BoolTheory().hasConst(x)

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(x) =>
        if (state.binding.contains(x)) {
          val cell = state.binding.apply(x)
          state.setRex(NameEx(cell.toString))
        } else {
          throw new RewriterException(s"${getClass.getSimpleName}: Variable $x is not assigned a value")
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
