package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{ApalacheInternalOper, TlaSetOper}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * Rewrites set membership tests: x \in S, x \in SUBSET S, and x \in [S -> T].
 *
 * @author
 *   Igor Konnov
 */
class SetInRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(op, NameEx(name), _) if op == TlaSetOper.in || op == ApalacheInternalOper.selectInSet =>
        ArenaCell.isValidName(name) || state.binding.contains(name)

      case OperEx(op, _, _) if op == TlaSetOper.in || op == ApalacheInternalOper.selectInSet =>
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
      case OperEx(op, NameEx(name), OperEx(TlaSetOper.enumSet, rhs))
          if op == TlaSetOper.in || op == ApalacheInternalOper.selectInSet =>
        val nextState = rewriter.rewriteUntilDone(state.setRex(rhs))
        val rhsCell = nextState.arena.findCellByNameEx(nextState.ex)
        val lhsCell = state.binding(name)
        val afterEqState = rewriter.lazyEq.cacheOneEqConstraint(nextState, lhsCell, rhsCell)
        // bugfix: safeEq may produce ValEx(TlaBool(false)) or ValEx(TlaBool(true)).
        rewriter.rewriteUntilDone(afterEqState.setRex(rewriter.lazyEq.safeEq(lhsCell, rhsCell)))

      case OperEx(op, elem, set) if op == TlaSetOper.in || op == ApalacheInternalOper.selectInSet =>
        val elemState = rewriter.rewriteUntilDone(state.setRex(elem))
        val elemCell = elemState.asCell
        val setState = rewriter.rewriteUntilDone(elemState.setRex(set))
        val setCell = setState.asCell
        setCell.cellType match {
          case CellTFrom(SetT1(_)) =>
            basicIn(setState, setCell, elemCell)

          case InfSetT(CellTFrom(IntT1))
              if setCell == setState.arena.cellNatSet() || setCell == setState.arena.cellIntSet() =>
            intOrNatSetIn(setState, setCell, elemCell, CellTFrom(IntT1))

          case PowSetT(SetT1(_)) =>
            powSetIn(setState, setCell, elemCell)

          case FinFunSetT(_, _) =>
            funSetIn(setState, setCell, elemCell)

          case _ =>
            throw new RewriterException("SetInRule is not implemented for type %s (found in %s)"
                  .format(setCell.cellType, state.ex), state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  protected def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
    def checkType: PartialFunction[(CellT, CellT), Unit] = {
      case (PowSetT(SetT1(expectedType)), CellTFrom(SetT1(actualType))) =>
        if (expectedType != actualType) {
          val msg = s"Unexpected types in SetInRule.powSetIn: expectedType = $expectedType, actualType = $actualType"
          throw new IllegalStateException(msg)
        }
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
      case CellTFrom(FunT1(_, _)) => () // OK
      case _                      => flagTypeError()
    }
    funsetCell.cellType match {
      case FinFunSetT(PowSetT(_), _) | FinFunSetT(FinFunSetT(_, _), _) =>
        flagTypeError()
      case _ => () // OK
    }
    val funsetDom = state.arena.getDom(funsetCell)
    val funsetCdm = state.arena.getCdm(funsetCell)
    var nextState = state
    nextState = nextState.updateArena(_.appendCell(BoolT1))
    val pred = nextState.arena.topCell
    val relation = nextState.arena.getCdm(funCell)

    // In the new implementation, a function is a relation { <<x, f[x]>> : x \in U }.
    // Check that \A t \in f: t[1] \in S /\ t[2] \in T, and
    // `DOMAIN f = S`, since the above only implies `DOMAIN f \subseteq S`
    def onPair(pair: ArenaCell): TBuilderInstruction = {
      val tupleElems = nextState.arena.getHas(pair)
      val (arg, res) = (tupleElems.head, tupleElems.tail.head)
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.selectInSet(arg.toBuilder, funsetDom.toBuilder)))
      val inDom = nextState.asCell
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.selectInSet(res.toBuilder, funsetCdm.toBuilder)))
      val inCdm = nextState.asCell
      // BUGFIX: check only those pairs that actually belong to the relation
      tla
        .or(tla.not(tla.selectInSet(pair.toBuilder, relation.toBuilder)), tla.and(inDom.toBuilder, inCdm.toBuilder))
    }
    val relElems = nextState.arena.getHas(relation)
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toBuilder, tla.and(relElems.map(onPair): _*)))

    // S = DOMAIN f
    val domainEx =
      tla
        .eql(
            funsetDom.toBuilder,
            tla.dom(funCell.toBuilder),
        )

    rewriter.rewriteUntilDone(
        nextState.setRex(
            tla.and(pred.toBuilder, domainEx)
        )
    )
  }

  protected def intOrNatSetIn(
      state: SymbState,
      setCell: ArenaCell,
      elemCell: ArenaCell,
      elemType: types.CellT): SymbState = {
    if (setCell == state.arena.cellIntSet()) {
      // Do nothing, it is just true. The type checker should have taken care of that.
      state.setRex(state.arena.cellTrue().toBuilder)
    } else {
      // i \in Nat <=> i >= 0
      assert(setCell == state.arena.cellNatSet())
      assert(elemType == CellTFrom(IntT1))
      val nextState = state.updateArena(_.appendCell(BoolT1))
      val pred = nextState.arena.topCell
      rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toBuilder, tla.ge(elemCell.toBuilder, tla.int(0))))
      nextState.setRex(pred.toBuilder)
    }
  }

  protected def basicIn(
      state: SymbState,
      setCell: ArenaCell,
      elemCell: ArenaCell): SymbState = {
    val potentialElems = state.arena.getHas(setCell)
    // The types of the element and the set may slightly differ, but they must be unifiable.
    // For instance, [a |-> 1] \in { [a |-> 2], [a |-> 3, b -> "foo"] }
    if (potentialElems.isEmpty) {
      // the set cell points to no other cell => return false
      state.setRex(state.arena.cellFalse().toBuilder)
    } else {
      val nextState = state.updateArena(_.appendCell(BoolT1))
      val pred = nextState.arena.topCell.toBuilder

      // cache equality constraints first
      val eqState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

      // inAndEq checks if elemCell is in setCell
      val elemsInAndEq = potentialElems.map(inAndEq(rewriter, _, elemCell, setCell, lazyEq = true))
      rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.or(elemsInAndEq: _*)))
      eqState.setRex(pred)
    }
  }
}
