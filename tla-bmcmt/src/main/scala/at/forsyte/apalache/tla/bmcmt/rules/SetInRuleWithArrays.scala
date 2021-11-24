package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.implicitConversions.Crossable
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.aux.SetMembershipFactory
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter, types}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

class SetInRuleWithArrays(rewriter: SymbStateRewriter) extends SetInRule(rewriter) {
  private val simplifier = new ConstSimplifierForSmt
  private val setMemFactory = new SetMembershipFactory(rewriter.solverContext.config.smtEncoding)

  override protected def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
    def checkType: PartialFunction[(CellT, CellT), Unit] = {
      case (PowSetT(FinSetT(expectedType)), FinSetT(actualType)) =>
        assert(expectedType == actualType)
    }
    // double check that the type finder did its job
    checkType(powsetCell.cellType, elemCell.cellType)

    val setElems = state.arena.getHas(elemCell)
    val powsetDomain = state.arena.getDom(powsetCell)
    val powsetDomainElems = state.arena.getHas(powsetDomain)
    // EqConstraints need to be generated, since missing in-relations, e.g. in sets of tuples, will lead to errors.
    // TODO: Inlining this method is pointless. We should consider handling tuples and other structures natively in SMT.
    var newState = rewriter.lazyEq.cacheEqConstraints(state, setElems cross powsetDomainElems)

    def isInPowset(setElem: ArenaCell): TlaEx = {
      newState = newState.updateArena(_.appendCell(BoolT()))
      val pred = newState.arena.topCell

      def isInAndEqSetElem(powsetDomainElem: ArenaCell) = {
        // powsetDomainElem \in powsetDomain /\ powsetDomainElem = setElem
        simplifier.simplifyShallow(tla.and(setMemFactory.mkReadMem(powsetDomainElem, powsetDomain),
                tla.eql(powsetDomainElem.toNameEx, setElem.toNameEx)))
      }

      val elemsInAndEqSetElem = powsetDomainElems.map(isInAndEqSetElem)
      // pred <=> (setElem \in elemCell => elemsInAndEqSetElem.1 \/ ... \/ elemsInAndEqSetElem.n)
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.equiv(pred.toNameEx,
                  tla.or(tla.not(setMemFactory.mkReadMem(setElem, elemCell)), tla.or(elemsInAndEqSetElem: _*)))))
      pred.toNameEx
    }

    val isSubset = simplifier.simplifyShallow(tla.and(setElems.map(isInPowset): _*))
    newState = newState.updateArena(_.appendCell(BoolT()))
    val pred = newState.arena.topCell.toNameEx
    rewriter.solverContext.assertGroundExpr(tla.eql(pred, isSubset))
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

      // EqConstraints need to be generated, since missing in-relations, e.g. in sets of tuples, will lead to errors.
      // TODO: Inlining this method is pointless. We should consider handling tuples and other structures natively in SMT.
      val eqState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

      def inAndEq(elem: ArenaCell) = {
        simplifier
          .simplifyShallow(tla.and(setMemFactory.mkReadMem(elem, setCell), tla.eql(elem.toNameEx, elemCell.toNameEx)))
      }

      val elemsInAndEq = potentialElems.map(inAndEq)
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.eql(pred, tla.or(elemsInAndEq: _*))))
      eqState.setRex(pred)
    }
  }
}
