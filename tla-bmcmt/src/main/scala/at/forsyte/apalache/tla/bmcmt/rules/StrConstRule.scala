package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.values.TlaStr

/**
  * Implements the rule SE-STR-CONST.
  *
  * @author Igor Konnov
  */
class StrConstRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaStr(_)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaStr(str)) =>
        val (newArena: Arena, newCell: ArenaCell) = rewriter.strValueCache.getOrCreate(state.arena, str)
        val finalState =
          state.setTheory(CellTheory())
            .setArena(newArena)
            .setRex(newCell.toNameEx)
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable")
    }
  }
}
