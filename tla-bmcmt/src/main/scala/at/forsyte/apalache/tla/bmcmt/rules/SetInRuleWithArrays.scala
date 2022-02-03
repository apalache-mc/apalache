package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.implicitConversions.Crossable
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, CellT, FinFunSetT, FinSetT, FunT, PowSetT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter, types}
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Rewrites set membership tests: x \in S, x \in SUBSET S, and x \in [S -> T].
 *
 * @author Rodrigo Otoni
 */
class SetInRuleWithArrays(rewriter: SymbStateRewriter) extends SetInRule(rewriter) {
  private val simplifier = new ConstSimplifierForSmt

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
        simplifier.simplifyShallow(tla.and(tla.apalacheSelectInSet(powsetDomainElem.toNameEx, powsetDomain.toNameEx),
                tla.eql(powsetDomainElem.toNameEx, setElem.toNameEx)))
      }

      val elemsInAndEqSetElem = powsetDomainElems.map(isInAndEqSetElem)
      // pred <=> (setElem \in elemCell => elemsInAndEqSetElem.1 \/ ... \/ elemsInAndEqSetElem.n)
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.equiv(pred.toNameEx,
                  tla.or(tla.not(tla.apalacheSelectInSet(setElem.toNameEx, elemCell.toNameEx)),
                      tla.or(elemsInAndEqSetElem: _*)))))
      pred.toNameEx
    }

    val isSubset = simplifier.simplifyShallow(tla.and(setElems.map(isInPowset): _*))
    newState = newState.updateArena(_.appendCell(BoolT()))
    val pred = newState.arena.topCell.toNameEx
    rewriter.solverContext.assertGroundExpr(tla.eql(pred, isSubset))
    newState.setRex(pred)
  }

  override protected def funSetIn(state: SymbState, funsetCell: ArenaCell, funCell: ArenaCell): SymbState = {
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
      case FinFunSetT(PowSetT(_), _) | FinFunSetT(FinFunSetT(_, _), _) => flagTypeError()
      case _                                                           => () // OK
    }

    val funCellDom = state.arena.getDom(funCell)
    val funsetDom = state.arena.getDom(funsetCell)
    val funsetDomElems = state.arena.getHas(funsetDom)
    val funsetCdm = state.arena.getCdm(funsetCell)
    var nextState = state

    nextState = nextState.updateArena(_.appendCell(BoolT()))
    val pred = nextState.arena.topCell

    def onFun(funsetDomElem: ArenaCell): TlaEx = {
      funsetCdm.cellType match {
        case _: PowSetT =>
          nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.appFun(funCell.toNameEx, funsetDomElem.toNameEx)))
          val funAppRes = nextState.arena.topCell
          val powSetDom = nextState.arena.getDom(funsetCdm)
          val subsetEq = tla.subseteq(funAppRes.toNameEx, powSetDom.toNameEx)
          nextState = rewriter.rewriteUntilDone(nextState.setRex(subsetEq))
          nextState.asCell.toNameEx

        case _ =>
          val funAppRes = tla.apalacheSelectInFun(funsetDomElem.toNameEx, funCell.toNameEx)
          tla.apalacheSelectInSet(funAppRes, funsetCdm.toNameEx)
      }
    }

    rewriter.solverContext.assertGroundExpr(tla.eql(funsetDom.toNameEx, funCellDom.toNameEx).typed(BoolT1()))
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toNameEx, tla.and(funsetDomElems map onFun: _*)))

    rewriter.rewriteUntilDone(nextState.setRex(pred.toNameEx))
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
      nextState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

      def inAndEq(elem: ArenaCell) = {
        simplifier
          .simplifyShallow(tla.and(tla.apalacheSelectInSet(elem.toNameEx, setCell.toNameEx),
                  tla.eql(elem.toNameEx, elemCell.toNameEx)))
      }

      val elemsInAndEq = potentialElems.map(inAndEq)
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.eql(pred, tla.or(elemsInAndEq: _*))))
      nextState.setRex(pred)
    }
  }
}
