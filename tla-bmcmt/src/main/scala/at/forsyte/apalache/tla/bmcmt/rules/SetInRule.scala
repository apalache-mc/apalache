package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.BoolType
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}

/**
  * Implements the rules: SE-SET-IN[1-2].
  *
  * @author Igor Konnov
   */
class SetInRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.in, _, _) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.in, elem, set) =>
        val elemState = rewriter.rewriteUntilDone(state.setRex(elem))
        val elemCell = elemState.arena.findCellByNameEx(elemState.ex)
        val setState = rewriter.rewriteUntilDone(elemState.setRex(set))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        var arena = setState.arena.appendCell(BoolType())
        val predCell = arena.topCell

        if (arena.isLinkedViaHas(setCell, elemCell)) {
          // SE-SET-IN1: the element cell is already in the arena, just check dynamic membership
          val cons = OperEx(TlaBoolOper.equiv,
            OperEx(TlaOper.eq, predCell.toNameEx, arena.cellTrue().toNameEx),
            OperEx(TlaSetOper.in, elemState.ex, setState.ex))
          setState.solverCtx.assertCellExpr(cons)
          setState.setArena(arena).setRex(predCell.toNameEx)
        } else {
          // SE-SET-IN2: general case
          setState
        }

      case _ =>
        throw new RewriterException("SetInRule is not applicable")
    }
  }
}
