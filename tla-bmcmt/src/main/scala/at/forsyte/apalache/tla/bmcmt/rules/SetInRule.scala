package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, PowSetT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}


/**
  * Implements the rules SE-SET-IN{1,2,3} and SE-IN-SUBSET1.
  *
  * @author Igor Konnov
  */
class SetInRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaSetOper.in, NameEx(name), _) =>
        (CellTheory().hasConst(name)
          || BoolTheory().hasConst(name)
          || IntTheory().hasConst(name)
          || state.binding.contains(name))

      case OperEx(TlaSetOper.in, _, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      // a common pattern x \in {y} that is equivalent to x = y, e.g., the assignment solver creates it
      case OperEx(TlaSetOper.in, NameEx(name), OperEx(TlaSetOper.enumSet, rhs)) =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs).setTheory(CellTheory()))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        val lhsCell = state.binding(name)
        val afterEqState = rewriter.lazyEq.cacheOneEqConstraint(nextState, lhsCell, rhsCell)
        val finalState = afterEqState
          .setTheory(BoolTheory())
          .setRex(rewriter.lazyEq.safeEq(lhsCell, rhsCell))
          .setBinding(nextState.binding + (name -> rhsCell)) // bind the cell to the name
        rewriter.coerce(finalState, state.theory)

      case OperEx(TlaSetOper.in, elem, set) =>
        // TODO: here we could benefit from the type inference phase
        // switch to cell theory
        val elemState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(elem))
        val elemCell = elemState.arena.findCellByNameEx(elemState.ex)
        val setState = rewriter.rewriteUntilDone(elemState.setRex(set))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        val finalState: SymbState = setCell.cellType match {
          case FinSetT(elemType) =>
            basicIn(setState, setCell, elemCell, elemType)

          case PowSetT(FinSetT(_)) =>
            powSetIn(setState, setCell, elemCell)

          case _ => throw new RewriterException("SetInRule is not implemented for type %s (found in %s)"
            .format(setCell.cellType, state.ex))
        }

        val coercedState = rewriter.coerce(finalState, state.theory)
        assert(coercedState.arena.cellCount >= finalState.arena.cellCount) // catching a tricky bug
        coercedState

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
    (powsetCell.cellType, elemCell.cellType) match {
      case (PowSetT(FinSetT(expectedType)), FinSetT(actualType)) =>
        def unif = expectedType.unify(actualType)
        if (unif.isEmpty) {
          // The types do not match, so we can safely return false.
          // TODO: flag a static warning?
          state.setRex(state.arena.cellFalse())
        } else {
          // delegate the work to \subseteq
          rewriter.lazyEq.subsetEq(state, elemCell, state.arena.getDom(powsetCell))
        }

      case t @ _ =>
        throw new RewriterException("Unexpected type: " + t)
    }
  }

  private def basicIn(state: SymbState, setCell: ArenaCell, elemCell: ArenaCell, elemType: types.CellT) = {
    val potentialElems = state.arena.getHas(setCell)
    if (!elemCell.cellType.comparableWith(elemType)) {
      // SE-SET-IN0: incompatible types => return false
      state.setTheory(BoolTheory())
        .setRex(NameEx(rewriter.solverContext.falseConst))
    } else if (potentialElems.isEmpty) {
      // SE-SET-IN1: the set cell points to no other cell => return false
      state.setTheory(BoolTheory())
        .setRex(NameEx(rewriter.solverContext.falseConst))
    } else {
      val pred = rewriter.solverContext.introBoolConst()
      if (state.arena.isLinkedViaHas(setCell, elemCell)) {
        // SE-SET-IN2: the element cell is already in the arena, just check dynamic membership
        rewriter.solverContext.assertGroundExpr(tla.eql(tla.name(pred), tla.in(elemCell, state.ex)))
        state.setTheory(BoolTheory()).setRex(NameEx(pred))
      } else {
        // SE-SET-IN3: general case, generate equality constraints, if needed, and use them
        // cache equality constraints first
        val eqState = rewriter.lazyEq.cacheEqConstraints(state, potentialElems.map((_, elemCell)))

        def inAndEq(elem: ArenaCell) = {
          tla.and(tla.in(elem, setCell), rewriter.lazyEq.safeEq(elem, elemCell)) // use lazy equality
        }

        val elemsInAndEq = potentialElems.map(inAndEq)
        rewriter.solverContext.assertGroundExpr(tla.eql(tla.name(pred), tla.or(elemsInAndEq: _*)))
        eqState.setTheory(BoolTheory()).setRex(NameEx(pred))
      }
    }
  }
}
