package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.InOpFactory
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
 * Rewrites set membership tests: x \in S, x \in SUBSET S, and x \in [S -> T].
 *
 * @author Igor Konnov
 */
class SetInRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val inOpFactory = new InOpFactory(rewriter.solverContext.config.smtEncoding)

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaSetOper.in, NameEx(name), _) =>
        ArenaCell.isValidName(name) || state.binding.contains(name)

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
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        val lhsCell = state.binding(name)
        val afterEqState = rewriter.lazyEq.cacheOneEqConstraint(nextState, lhsCell, rhsCell)
        // bugfix: safeEq may produce ValEx(TlaBool(false)) or ValEx(TlaBool(true)).
        rewriter.rewriteUntilDone(afterEqState.setRex(rewriter.lazyEq.safeEq(lhsCell, rhsCell)))

      case OperEx(TlaSetOper.in, elem, set) =>
        val elemState = rewriter.rewriteUntilDone(state.setRex(elem))
        val elemCell = elemState.asCell
        val setState = rewriter.rewriteUntilDone(elemState.setRex(set))
        val setCell = setState.asCell
        setCell.cellType match {
          case FinSetT(elemType) =>
            basicIn(setState, setCell, elemCell, elemType)

          case InfSetT(IntT()) if setCell == setState.arena.cellNatSet() || setCell == setState.arena.cellIntSet() =>
            intOrNatSetIn(setState, setCell, elemCell, IntT())

          case PowSetT(FinSetT(_)) =>
            powSetIn(setState, setCell, elemCell)

          case FinFunSetT(_, _) =>
            funSetIn(setState, setCell, elemCell)

          case _ =>
            throw new RewriterException(
                "SetInRule is not implemented for type %s (found in %s)"
                  .format(setCell.cellType, state.ex), state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  protected def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
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
  protected def funSetIn(state: SymbState, funsetCell: ArenaCell, funCell: ArenaCell): SymbState = {
    // checking whether f \in [S -> T]
    def flagTypeError(): Nothing = {
      val msg = s"Not implemented (open an issue): f \\in S for f: %s and S: %s."
        .format(funCell.cellType, funsetCell.cellType)
      throw new RewriterException(msg, state.ex)
    }

    funCell.cellType match {
      case FunT(FinSetT(_), _) => () // OK
      case _                   => flagTypeError()
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
      nextState = rewriter.rewriteUntilDone(nextState.setRex(inOpFactory.mkAccessOp(arg, funsetDom)))
      val inDom = nextState.asCell
      nextState = rewriter.rewriteUntilDone(nextState.setRex(inOpFactory.mkAccessOp(res, funsetCdm)))
      val inCdm = nextState.asCell
      // BUGFIX: check only those pairs that actually belong to the relation
      tla.or(inOpFactory.mkUnchangedOp(pair.toNameEx, relation.toNameEx), tla.and(inDom.toNameEx, inCdm.toNameEx))
    }

    val relElems = nextState.arena.getHas(relation)
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toNameEx, tla.and(relElems map onPair: _*)))

    rewriter.rewriteUntilDone(nextState.setRex(pred.toNameEx))
  }

  protected def intOrNatSetIn(state: SymbState, setCell: ArenaCell, elemCell: ArenaCell,
      elemType: types.CellT): SymbState = {
    if (setCell == state.arena.cellIntSet()) {
      // Do nothing, it is just true. The type checker should have taken care of that.
      state.setRex(state.arena.cellTrue().toNameEx)
    } else {
      // i \in Nat <=> i >= 0
      assert(setCell == state.arena.cellNatSet())
      assert(elemType == IntT())
      var nextState = state.updateArena(_.appendCell(BoolT()))
      val pred = nextState.arena.topCell
      rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toNameEx, tla.ge(elemCell.toNameEx, tla.int(0))))
      nextState.setRex(pred.toNameEx)
    }
  }

  protected def basicIn(state: SymbState, setCell: ArenaCell, elemCell: ArenaCell, elemType: types.CellT): SymbState = {
    val potentialElems = state.arena.getHas(setCell)
    // The types of the element and the set may slightly differ, but they must be unifiable.
    // For instance, [a |-> 1] \in { [a |-> 2], [a |-> 3, b -> "foo"] }
    assert(elemCell.cellType.unify(elemType).nonEmpty)
    if (potentialElems.isEmpty) {
      // the set cell points to no other cell => return false
      state.setRex(state.arena.cellFalse().toNameEx)
    } else {
      var nextState = state.updateArena(_.appendCell(BoolT()))
      val pred = nextState.arena.topCell.toNameEx

      // cache equality constraints first
      val eqState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

      def inAndEq(elem: ArenaCell) = {
        tla.and(inOpFactory.mkAccessOp(elem, setCell), rewriter.lazyEq.safeEq(elem, elemCell)) // use lazy equality
      }

      val elemsInAndEq = potentialElems.map(inAndEq)
      rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.or(elemsInAndEq: _*)))
      eqState.setRex(pred)
    }
  }
}
