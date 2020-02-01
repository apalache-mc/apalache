package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}


/**
  * Implements the rules SE-SET-IN{1,2,3}, SE-IN-FUNSET, and SE-IN-SUBSET1.
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

  // TODO: x \in S should be equivalent to SkolemExists(\E t \in S: x = t)
  // This is only true for the positive occurences of x \in S!
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
        rewriter.coerce(finalState, state.theory)

      case OperEx(TlaSetOper.in, elem, set) =>
        // TODO: remove theories, see https://github.com/konnov/apalache/issues/22
        // switch to cell theory
        val elemState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(elem))
        val elemCell = elemState.asCell
        val setState = rewriter.rewriteUntilDone(elemState.setRex(set))
        val setCell = setState.asCell
        val finalState: SymbState = setCell.cellType match {
          case FinSetT(elemType) =>
            if (setCell != setState.arena.cellNatSet() && setCell != setState.arena.cellIntSet()) {
              basicIn(setState, setCell, elemCell, elemType)
            } else {
              intOrNatSetIn(setState, setCell, elemCell, elemType)
            }

          case PowSetT(FinSetT(_)) =>
            powSetIn(setState, setCell, elemCell)

          case FinFunSetT(_, _) =>
            funSetIn(setState, setCell, elemCell)

          case _ => throw new RewriterException("SetInRule is not implemented for type %s (found in %s)"
            .format(setCell.cellType, state.ex), state.ex)
        }

        val coercedState = rewriter.coerce(finalState, state.theory)
        assert(coercedState.arena.cellCount >= finalState.arena.cellCount) // catching a tricky bug
        coercedState

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
    def checkType: PartialFunction[(CellT, CellT), Unit] = {
      case (PowSetT(FinSetT(expectedType)), FinSetT(actualType)) =>
        assert(expectedType == actualType)
    }
    // double check that the type finder did its job
    checkType(powsetCell.cellType, elemCell.cellType)
    // delegate the work to \subseteq
    rewriter.lazyEq.subsetEq(state, elemCell, state.arena.getDom(powsetCell))
  }

  // TODO: pick a function from funsetCell and check for function equality
  private def funSetIn(state: SymbState, funsetCell: ArenaCell, funCell: ArenaCell): SymbState = {
    // checking whether f \in [S -> T]
    def flagTypeError(): Nothing = {
      val msg = s"Not implemented (open an issue): f \\in S for f: %s and S: %s."
        .format(funCell.cellType, funsetCell.cellType)
      throw new RewriterException(msg, state.ex)
    }
    funCell.cellType match {
      case FunT(FinSetT(_), _) => () // OK
      case _ => flagTypeError()
    }
    funsetCell.cellType match {
      case FinFunSetT(PowSetT(_), _) | FinFunSetT(FinFunSetT(_, _), _) =>
        flagTypeError()
      case _ => () // OK
    }
    val funsetDom = state.arena.getDom(funsetCell)
    val funsetCdm = state.arena.getCdm(funsetCell)
    var nextState = state
    nextState = nextState.updateArena(_.appendCell(BoolT()))
    val pred = nextState.arena.topCell
    val relation = nextState.arena.getCdm(funCell)
    // In the new implementation, a function is a relation { <<x, f[x]>> : x \in U }.
    // Check that \A t \in f: t[1] \in S /\ t[2] \in T.
    def onPair(pair: ArenaCell): TlaEx = {
      val tupleElems = nextState.arena.getHas(pair)
      val (arg, res) = (tupleElems.head, tupleElems.tail.head)
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.in(arg, funsetDom)))
      val inDom = nextState.asCell
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.in(res, funsetCdm)))
      val inCdm = nextState.asCell
      // BUGFIX: check only those pairs that actually belong to the relation
      tla.or(tla.notin(pair, relation), tla.and(inDom, inCdm))
    }

    val relElems = nextState.arena.getHas(relation)
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred, tla.and(relElems map onPair :_*)))

    rewriter.rewriteUntilDone(nextState.setRex(pred).setTheory(CellTheory()))
  }

  private def intOrNatSetIn(state: SymbState, setCell: ArenaCell, elemCell: ArenaCell, elemType: types.CellT): SymbState = {
    if (setCell == state.arena.cellIntSet()) {
      // Do nothing, it is just true. The type checker should have taken care of that.
      state.setRex(state.arena.cellTrue())
    } else {
      // i \in Nat <=> i >= 0
      assert(setCell == state.arena.cellNatSet())
      assert(elemType == IntT())
      var nextState = state.updateArena(_.appendCell(BoolT()))
      val pred = nextState.arena.topCell
      rewriter.solverContext.assertGroundExpr(tla.equiv(pred, tla.ge(elemCell, tla.int(0))))
      nextState.setRex(pred).setTheory(CellTheory())
    }
  }

  private def basicIn(state: SymbState, setCell: ArenaCell, elemCell: ArenaCell, elemType: types.CellT) = {
    val potentialElems = state.arena.getHas(setCell)
    assert(elemCell.cellType == elemType) // otherwise, type finder is incorrect
    if (potentialElems.isEmpty) {
      // SE-SET-IN1: the set cell points to no other cell => return false
//      state.setTheory(BoolTheory()).setRex(NameEx(SolverContext.falseConst))
      state.setTheory(CellTheory()).setRex(state.arena.cellFalse())
    } else {
      var nextState = state.updateArena(_.appendCell(BoolT()))
      val pred = nextState.arena.topCell.toNameEx
      if (state.arena.isLinkedViaHas(setCell, elemCell)) {
        // SE-SET-IN2: the element cell is already in the arena, just check dynamic membership
        rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.in(elemCell, state.ex)))
        nextState.setTheory(CellTheory()).setRex(pred)
      } else {
        // SE-SET-IN3: general case, generate equality constraints, if needed, and use them
        // cache equality constraints first
        val eqState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

        def inAndEq(elem: ArenaCell) = {
          tla.and(tla.in(elem, setCell), rewriter.lazyEq.safeEq(elem, elemCell)) // use lazy equality
        }

        val elemsInAndEq = potentialElems.map(inAndEq)
        rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.or(elemsInAndEq: _*)))
        eqState.setTheory(CellTheory()).setRex(pred)
      }
    }
  }
}
