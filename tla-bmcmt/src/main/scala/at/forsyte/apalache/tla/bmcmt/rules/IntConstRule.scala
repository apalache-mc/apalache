package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
 * Rewrites integer constants.
 *
 * @author Igor Konnov
 */
class IntConstRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaInt(_)) => true
      case _                => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaInt(n)) =>
        val (newArena: Arena, intCell: ArenaCell) = rewriter.intValueCache.getOrCreate(state.arena, n)
        state
          .setArena(newArena)
          .setRex(intCell.toNameEx)

      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable", state.ex)
    }
  }
}
