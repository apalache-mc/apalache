package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.implicitConversions.Crossable
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter, types}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

class SetInRuleWithArrays(rewriter: SymbStateRewriter) extends SetInRule(rewriter) {
  private val simplifier = new ConstSimplifierForSmt

  override protected def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
    def checkType: PartialFunction[(CellT, CellT), Unit] = {
      case (PowSetT(FinSetT(expectedType)), FinSetT(actualType)) =>
        assert(expectedType == actualType)
    }
    // double check that the type finder did its job
    checkType(powsetCell.cellType, elemCell.cellType)

    val leftElems = state.arena.getHas(elemCell)
    val rightElem = state.arena.getDom(powsetCell)
    val rightElems = state.arena.getHas(rightElem)
    var newState = rewriter.lazyEq.cacheEqConstraints(state, leftElems cross rightElems) // cache all the equalities

    def isInRight(leftElem: ArenaCell): TlaEx = {
      newState = newState.updateArena(_.appendCell(BoolT()))
      val pred = newState.arena.topCell

      def isIn2(rightElem2: ArenaCell) = {
        (tla.and(tla.in(rightElem2.toNameEx, rightElem.toNameEx), tla.eql(rightElem2.toNameEx, leftElem.toNameEx)))
      }
      val elemsInAndEq = state.arena.getHas(rightElem).map(isIn2)
      val opElemsInAndEq = tla.or(elemsInAndEq: _*)
      rewriter.solverContext
        .assertGroundExpr((tla.equiv(pred.toNameEx,
                    tla.and(tla.in(leftElem.toNameEx, elemCell.toNameEx), opElemsInAndEq))))
      pred.toNameEx
    }

    val isSubset = (tla.and(leftElems.map(isInRight): _*))

    newState = newState.updateArena(_.appendCell(BoolT()))
    val pred = newState.arena.topCell.toNameEx

    // direct SMT equality
    val eq = (tla.eql(pred, isSubset))
    rewriter.solverContext.assertGroundExpr(eq)
    newState.setRex(pred)
  }

  // TODO: update when functions are supported by SMT arrays
  override protected def funSetIn(state: SymbState, funsetCell: ArenaCell, funCell: ArenaCell): SymbState = {
    super.funSetIn(state, funsetCell, funCell)
  }

  override protected def basicIn(state: SymbState, setCell: ArenaCell, elemCell: ArenaCell,
      elemType: types.CellT): SymbState = {
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
      // change for smt tuples later? Keeping lazyEq use for now.
      val eqState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

      def inAndEq(elem: ArenaCell) = {
        tla.and(tla.in(elem.toNameEx, setCell.toNameEx), tla.eql(elem.toNameEx, elemCell.toNameEx))
      }

      val elemsInAndEq = potentialElems.map(inAndEq)
      rewriter.solverContext.assertGroundExpr(tla.eql(pred, tla.or(elemsInAndEq: _*)))
      eqState.setRex(pred)
    }
  }
}
