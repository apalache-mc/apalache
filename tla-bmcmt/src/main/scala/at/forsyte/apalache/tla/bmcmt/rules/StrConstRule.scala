package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
 * Rewrites a string literal, e.g., "hello".
 *
 * @author Igor Konnov
 */
class StrConstRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaStr(_)) => true
      case _                => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaStr(str)) =>
        val (newArena: Arena, newCell: ArenaCell) = rewriter.strValueCache.getOrCreate(state.arena, str)
        state
          .setArena(newArena)
          .setRex(newCell.toNameEx)

      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable", state.ex)
    }
  }
}
