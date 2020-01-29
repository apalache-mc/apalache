package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.ValEx
import at.forsyte.apalache.tla.lir.values.TlaInt

/**
  * Implements the rule SE-INT-CONST.
  *
  * @author Igor Konnov
  */
class IntConstRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case ValEx(TlaInt(_)) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ValEx(TlaInt(n)) =>
        if (!n.isValidInt) {
          throw new RewriterException(s"BigInt $n does not fit into integer range. Do not know how to translate in SMT.", state.ex)
        }
        val (newArena: Arena, intCell: ArenaCell) = rewriter.intValueCache.getOrCreate(state.arena, n.toInt)
        val finalState =
          state.setArena(newArena)
            .setRex(intCell.toNameEx)
            .setTheory(CellTheory())
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException(getClass.getSimpleName + " is not applicable", state.ex)
    }
  }
}
