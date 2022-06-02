package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.implicitConversions.Crossable
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, RealT1, SetT1, StrT1, TlaEx, VarT1}

/**
 * Rewrites set membership tests: x \in S, x \in SUBSET S, and x \in [S -> T].
 *
 * @author
 *   Rodrigo Otoni
 */
class SetInRuleWithArrays(rewriter: SymbStateRewriter) extends SetInRule(rewriter) {
  private val simplifier = new ConstSimplifierForSmt

  override protected def powSetIn(state: SymbState, powsetCell: ArenaCell, elemCell: ArenaCell): SymbState = {
    def checkType: PartialFunction[(CellT, CellT), Unit] = {
      case (PowSetT(SetT1(expectedType)), CellTFrom(SetT1(actualType))) =>
        assert(expectedType == actualType)
    }
    // double check that the type finder did its job
    checkType(powsetCell.cellType, elemCell.cellType)

    val setElems = state.arena.getHas(elemCell)
    val powsetDomain = state.arena.getDom(powsetCell)
    val powsetDomainElems = state.arena.getHas(powsetDomain)
    // EqConstraints need to be generated, since missing in-relations, e.g. in sets of tuples, will lead to errors.
    // TODO: Inlining this method is pointless. We should consider handling tuples and other structures natively in SMT.
    var newState = rewriter.lazyEq.cacheEqConstraints(state, setElems.cross(powsetDomainElems))

    def isInPowset(setElem: ArenaCell): TlaEx = {
      newState = newState.updateArena(_.appendCell(BoolT1))
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
    newState = newState.updateArena(_.appendCell(BoolT1))
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
      case CellTFrom(FunT1(_, _)) => () // OK
      case _                      => flagTypeError()
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

    nextState = nextState.updateArena(_.appendCell(BoolT1))
    val pred = nextState.arena.topCell

    def onFun(funsetDomElem: ArenaCell): TlaEx = {
      funsetCdm.cellType match {
        case _: PowSetT =>
          nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.appFun(funCell.toNameEx, funsetDomElem.toNameEx)))
          val funAppRes = nextState.asCell
          val powSetDom = nextState.arena.getDom(funsetCdm)
          val subsetEq = tla.subseteq(funAppRes.toNameEx, powSetDom.toNameEx)
          nextState = rewriter.rewriteUntilDone(nextState.setRex(subsetEq))
          nextState.asCell.toNameEx

        case _ =>
          val funAppRes = tla.apalacheSelectInFun(funsetDomElem.toNameEx, funCell.toNameEx)
          tla.apalacheSelectInSet(funAppRes, funsetCdm.toNameEx)
      }
    }

    val domainEx = tla.eql(funsetDom.toNameEx, funCellDom.toNameEx)
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toNameEx, tla.and(funsetDomElems.map(onFun): _*)))

    rewriter.rewriteUntilDone(nextState.setRex(tla.and(pred.toNameEx, domainEx)))
  }

  override protected def basicIn(
      state: SymbState,
      setCell: ArenaCell,
      elemCell: ArenaCell): SymbState = {
    val potentialElems = state.arena.getHas(setCell)
    // The types of the element and the set may slightly differ, but they must be unifiable.
    // For instance, [a |-> 1] \in { [a |-> 2], [a |-> 3, b -> "foo"] }
    if (potentialElems.isEmpty) {
      // the set cell points to no other cell => return false
      state.setRex(state.arena.cellFalse().toNameEx)
    } else {
      var nextState = state.updateArena(_.appendCell(BoolT1))
      val pred = nextState.arena.topCell.toNameEx

      // For types that support SMT equality, we use that directly. For those that don't, we use lazy equality.
      if (supportsSMTEq(elemCell.cellType)) {
        val eql = tla.eql(pred, tla.apalacheSelectInSet(elemCell.toNameEx, setCell.toNameEx))
        rewriter.solverContext.assertGroundExpr(eql)
        nextState.setRex(pred)
      } else {
        // EqConstraints need to be generated, since missing in-relations, e.g. in sets of tuples, will lead to errors.
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

        def inAndEq(elem: ArenaCell) = {
          val select = tla.apalacheSelectInSet(elem.toNameEx, setCell.toNameEx)
          val eql = tla.eql(elem.toNameEx, elemCell.toNameEx)
          simplifier.simplifyShallow(tla.and(select, eql))
        }

        val elemsInAndEq = potentialElems.map(inAndEq)
        rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.eql(pred, tla.or(elemsInAndEq: _*))))
        nextState.setRex(pred)
      }
    }
  }

  private def supportsSMTEq(cellType: CellT): Boolean = {
    cellType match {
      case CellTFrom(_ @IntT1 | RealT1 | BoolT1 | StrT1 | ConstT1(_) | VarT1(_)) =>
        true
      case _ => false
    }
  }
}
