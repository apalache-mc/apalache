package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.NameEx

/**
  * Substitutes a bound name with a cell. For instance, it substitutes a name that is declared with VARIABLE or CONSTANT,
  * as well as bound variables declared with \A, \E, set operations, etc.
  *
  * @author Igor Konnov
  */
class SubstRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case NameEx(x) =>
        // make sure that x is not an SMT constant, but a variable name
        !ArenaCell.isValidName(x)

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case NameEx(x) =>
        if (state.binding.contains(x)) {
          val cell = state.binding(x)
          state.setRex(NameEx(cell.toString))
        } else {
          throw new RewriterException(
            s"${getClass.getSimpleName}: Variable $x is not assigned a value",
            state.ex
          )
        }

      case _ =>
        throw new RewriterException(
          "%s is not applicable".format(getClass.getSimpleName),
          state.ex
        )
    }
  }
}
