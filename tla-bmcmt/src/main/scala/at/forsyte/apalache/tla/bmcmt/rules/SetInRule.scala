package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.BoolType
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}

/**
  * Implements the rules: SE-SET-IN{1,2,3}.
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
      case OperEx(TlaSetOper.in, cand, set) =>
        val candState = rewriter.rewriteUntilDone(state.setRex(cand))
        val candCell = candState.arena.findCellByNameEx(candState.ex)
        val setState = rewriter.rewriteUntilDone(candState.setRex(set))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        val potentialElems = setState.arena.getHas(setCell)

        if (potentialElems.isEmpty) {
          // SE-SET-IN1: the set cell points to no other cell => return false
          setState.setRex(setState.arena.cellFalse().toNameEx)
        } else {
          var arena = setState.arena.appendCell(BoolType())
          val predCell = arena.topCell

          val cons =
            if (arena.isLinkedViaHas(setCell, candCell)) {
              // SE-SET-IN2: the element cell is already in the arena, just check dynamic membership
              OperEx(TlaBoolOper.equiv,
                OperEx(TlaOper.eq, predCell.toNameEx, arena.cellTrue().toNameEx),
                OperEx(TlaSetOper.in, candState.ex, setState.ex))
            } else {
              // SE-SET-IN3: general case, generate equality constraints, if needed, and use them
              def inAndEq(elem: ArenaCell) = {
                OperEx(TlaBoolOper.and,
                  OperEx(TlaSetOper.in, elem.toNameEx, setCell.toNameEx),
                  arena.lazyEquality.mkEquality(arena, elem, candCell))
              }

              val elemsInAndEq = arena.getHas(setCell).map(inAndEq)
              OperEx(TlaBoolOper.equiv,
                OperEx(TlaOper.eq, predCell.toNameEx, arena.cellTrue().toNameEx),
                OperEx(TlaBoolOper.or, elemsInAndEq: _*))
            }
          setState.solverCtx.assertCellExpr(cons)
          setState.setArena(arena).setRex(predCell.toNameEx)

        }

      case _ =>
        throw new RewriterException("SetInRule is not applicable")
    }
  }
}
