package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

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
        // switch to cell theory
        val candState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(cand))
        val candCell = candState.arena.findCellByNameEx(candState.ex)
        val setState = rewriter.rewriteUntilDone(candState.setRex(set))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        val potentialElems = setState.arena.getHas(setCell)

        val finalState =
          if (potentialElems.isEmpty) {
            // SE-SET-IN1: the set cell points to no other cell => return false
            setState.setTheory(BoolTheory())
              .setRex(NameEx(setState.solverCtx.falseConst))
          } else {
            val newArena = setState.arena
            val pred = state.solverCtx.introBoolConst()
            val cons =
              if (newArena.isLinkedViaHas(setCell, candCell)) {
                // SE-SET-IN2: the element cell is already in the arena, just check dynamic membership
                OperEx(TlaOper.eq,
                  NameEx(pred),
                  OperEx(TlaSetOper.in, candState.ex, setState.ex))
              } else {
                // SE-SET-IN3: general case, generate equality constraints, if needed, and use them
                def inAndEq(elem: ArenaCell) = {
                  OperEx(TlaBoolOper.and,
                    OperEx(TlaSetOper.in, elem.toNameEx, setCell.toNameEx),
                    newArena.lazyEquality.mkEquality(newArena, elem, candCell))
                }

                val elemsInAndEq = potentialElems.map(inAndEq)
                OperEx(TlaOper.eq,
                  NameEx(pred),
                  OperEx(TlaBoolOper.or, elemsInAndEq: _*))
              }

            setState.solverCtx.assertGroundExpr(cons)
            setState.setTheory(BoolTheory())
                .setArena(newArena).setRex(NameEx(pred))
          }

        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("SetInRule is not applicable")
    }
  }
}
