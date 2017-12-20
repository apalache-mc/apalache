package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
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
        val elemType = setCell.cellType match {
          case FinSetT(et) => et
          case _ => throw new RewriterException("Unexpected set type: " + setCell.cellType)
        }

        val finalState =
          if (!candCell.cellType.comparableWith(elemType)) {
            // SE-SET-IN0: incompatible types => return false
            setState.setTheory(BoolTheory())
              .setRex(NameEx(setState.solverCtx.falseConst))
          } else if (potentialElems.isEmpty) {
            // SE-SET-IN1: the set cell points to no other cell => return false
            setState.setTheory(BoolTheory())
              .setRex(NameEx(setState.solverCtx.falseConst))
          } else {
            val newArena = setState.arena
            val pred = state.solverCtx.introBoolConst()
              if (newArena.isLinkedViaHas(setCell, candCell)) {
                // SE-SET-IN2: the element cell is already in the arena, just check dynamic membership
                setState.solverCtx.assertGroundExpr(tla.eql(tla.name(pred), tla.in(candState.ex, setState.ex)))
                setState.setTheory(BoolTheory())
                  .setArena(newArena).setRex(NameEx(pred))
              } else {
                // SE-SET-IN3: general case, generate equality constraints, if needed, and use them
                // cache equality constraints first
                val eqState = rewriter.lazyEq.cacheEqConstraints(setState, potentialElems.map((_, candCell)))

                def inAndEq(elem: ArenaCell) = {
                  tla.and(tla.in(elem, setCell), rewriter.lazyEq.safeEq(elem, candCell)) // use lazy equality
                }

                val elemsInAndEq = potentialElems.map(inAndEq)
                eqState.solverCtx.assertGroundExpr(tla.eql(tla.name(pred), tla.or(elemsInAndEq: _*)))
                eqState.setTheory(BoolTheory()).setArena(newArena).setRex(NameEx(pred))
              }
          }

        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("SetInRule is not applicable")
    }
  }
}
