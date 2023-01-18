package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.implicitConversions.Crossable
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

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

    def isInPowset(setElem: ArenaCell): TBuilderInstruction = {
      newState = newState.updateArena(_.appendCell(BoolT1))
      val pred = newState.arena.topCell

      def isInAndEqSetElem(powsetDomainElem: ArenaCell): TBuilderInstruction = {
        // powsetDomainElem \in powsetDomain /\ powsetDomainElem = setElem
        tla
          .and(tla.selectInSet(powsetDomainElem.toBuilder, powsetDomain.toBuilder),
              tla.eql(powsetDomainElem.toBuilder, setElem.toBuilder))
          .map(simplifier.simplifyShallow)
      }

      val elemsInAndEqSetElem = powsetDomainElems.map(isInAndEqSetElem)
      // pred <=> (setElem \in elemCell => elemsInAndEqSetElem.1 \/ ... \/ elemsInAndEqSetElem.n)
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.equiv(pred.toBuilder,
                  tla.or(tla.not(tla.selectInSet(setElem.toBuilder, elemCell.toBuilder)),
                      tla.or(elemsInAndEqSetElem: _*)))))
      pred.toBuilder
    }

    val isSubset = tla.and(setElems.map(isInPowset): _*).map(simplifier.simplifyShallow)
    newState = newState.updateArena(_.appendCell(BoolT1))
    val pred = newState.arena.topCell.toBuilder
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

    // This method checks if f(x) \in T, for a given x
    // The goal is to ensure that \forall x \in DOMAIN f : f(x) \in T, by applying it to every arg \in DOMAIN f
    def onFun(funsetDomElem: ArenaCell): TBuilderInstruction = {
      funsetCdm.cellType match {
        case _: PowSetT =>
          nextState = rewriter
            .rewriteUntilDone(nextState.setRex(tla.app(funCell.toBuilder, funsetDomElem.toBuilder)))
          val funAppRes = nextState.asCell
          val powSetDom = nextState.arena.getDom(funsetCdm)
          val subsetEq = tla.subseteq(funAppRes.toBuilder, powSetDom.toBuilder)
          nextState = rewriter.rewriteUntilDone(nextState.setRex(subsetEq))
          nextState.asCell.toBuilder

        case _ =>
          val funAppRes = tla.selectInFun(funsetDomElem.toBuilder, funCell.toBuilder)
          tla.selectInSet(funAppRes, funsetCdm.toBuilder)
      }
    }

    val domainEx = tla.eql(funsetDom.toBuilder, funCellDom.toBuilder)
    rewriter.solverContext.assertGroundExpr(tla.equiv(pred.toBuilder, tla.and(funsetDomElems.map(onFun): _*)))

    rewriter.rewriteUntilDone(nextState.setRex(tla.and(pred.toBuilder, domainEx)))
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
      state.setRex(state.arena.cellFalse().toBuilder)
    } else {
      var nextState = state.updateArena(_.appendCell(BoolT1))
      val pred = nextState.arena.topCell.toBuilder

      // For types that support SMT equality, we use that directly. For those that don't, we use lazy equality.
      if (supportsSMTEq(elemCell.cellType)) {
        val eql = tla.eql(pred, tla.selectInSet(elemCell.toBuilder, setCell.toBuilder))
        rewriter.solverContext.assertGroundExpr(eql)
        nextState.setRex(pred)
      } else {
        // EqConstraints need to be generated, since missing in-relations, e.g. in sets of tuples, will lead to errors.
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, potentialElems.map((_, elemCell)))

        // inAndEq checks if elemCell is in setCell
        val elemsInAndEq = potentialElems.map(inAndEq(rewriter, _, elemCell, setCell, lazyEq = false))
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
