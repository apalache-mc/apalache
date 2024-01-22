package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.implicitConversions.Crossable
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{CellTFrom, InfSetT, PowSetT, UnknownT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, RewritingRule, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx, RecT1, SetT1, TlaEx, TupT1}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

// TODO: \subseteq is rewritten in Keramelizer
// Remove after the delegation to this rule in `CherryPick` is removed
class SetInclusionRuleWithArrays(rewriter: SymbStateRewriter) extends RewritingRule {
  private val simplifier = new ConstSimplifierForSmt

  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaSetOper.subseteq, _, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.subseteq, left, right) =>
        val leftState = rewriter.rewriteUntilDone(state.setRex(left))
        val leftCell = leftState.arena.findCellByNameEx(leftState.ex)
        val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
        val rightCell = rightState.arena.findCellByNameEx(rightState.ex)
        (leftCell.cellType, rightCell.cellType) match {
          case (CellTFrom(SetT1(_)), CellTFrom(SetT1(_))) =>
            subset(rightState, leftCell, rightCell, false)

          case (CellTFrom(SetT1(_)), InfSetT(_)) =>
            subset(rightState, leftCell, rightCell, false)

          case (CellTFrom(SetT1(SetT1(t1))), PowSetT(SetT1(t2))) =>
            if (t1 != t2) {
              throw new RewriterException("Unexpected set types: %s and %s in %s"
                    .format(t1, t2, state.ex), state.ex)
            } else {
              subset(rightState, leftCell, rightCell, true)
            }

          case _ =>
            throw new RewriterException("Unexpected set types: %s and %s in %s"
                  .format(leftCell.cellType, rightCell.cellType, state.ex), state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  // TODO: similar to SetInRuleWithArrays.powSetIn, potential for refactoring.
  private def subset(
      state: SymbState,
      leftCell: ArenaCell,
      rightCell: ArenaCell,
      rightIsPowSet: Boolean): SymbState = {
    val leftElems = state.arena.getHas(leftCell)
    val leftElemsElems = leftElems.flatMap(state.arena.getHas)
    val rightElemOrDomain = if (rightIsPowSet) state.arena.getDom(rightCell) else rightCell
    val rightElemOrDomainElems = state.arena.getHas(rightElemOrDomain)

    var newState = state

    // If rightCell is a power set, we check if the elements in the sets of leftCell are in the domain of rightCell.
    // Otherwise, we check if the elements of leftCell are in rightCell, in order to establish the subset relation.
    if (rightIsPowSet) {
      def eachElem(state: SymbState, elem: ArenaCell): SymbState = {
        val newState = subset(state, elem, rightElemOrDomain, false)
        val outOrSubsetEq = tla.or(tla.not(tla.apalacheSelectInSet(elem.toNameEx, leftCell.toNameEx)), newState.ex)
        newState.setRex(outOrSubsetEq)
      }

      leftElems.foldLeft(newState)(eachElem)
    } else {
      // EqConstraints need to be generated, since missing in-relations, e.g. in sets of tuples, will lead to errors.
      // TODO: Inlining this method is pointless. We should consider handling tuples and other structures natively in SMT.
      val leftElemsElemsType = if (leftElemsElems.nonEmpty) leftElemsElems.head.cellType else UnknownT
      val needsInRelations = leftElemsElemsType match {
        case CellTFrom(TupT1(_)) | CellTFrom(RecT1(_)) => true
        case _                                         => false
      }

      if (needsInRelations) {
        newState = rewriter.lazyEq.cacheEqConstraints(state, leftElemsElems.cross(rightElemOrDomainElems))
      }

      def isInRightSet(leftElem: ArenaCell): TlaEx = {
        def isInAndEqLeftElem(rightElemOrDomainElem: ArenaCell) = {
          // rightElemOrDomainElem \in rightElemOrDomain /\ rightElemOrDomainElem = leftElem
          simplifier.simplifyShallow(tla.and(tla.apalacheSelectInSet(rightElemOrDomainElem.toNameEx,
                      rightElemOrDomain.toNameEx), tla.eql(rightElemOrDomainElem.toNameEx, leftElem.toNameEx)))
        }

        newState = newState.updateArena(_.appendCell(BoolT1))
        val pred = newState.arena.topCell
        val elemsInAndEqLeftElem = rightElemOrDomainElems.map(isInAndEqLeftElem)

        // pred <=> (leftElem \in leftCell => elemsInAndEqLeftElem.1 \/ ... \/ elemsInAndEqLeftElem.n)
        rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.equiv(pred.toNameEx,
                    tla.or(tla.not(tla.apalacheSelectInSet(leftElem.toNameEx, leftCell.toNameEx)),
                        tla.or(elemsInAndEqLeftElem: _*)))))
        pred.toNameEx
      }

      val isSubset = tla.and(leftElems.map(isInRightSet): _*)
      newState = newState.updateArena(_.appendCell(BoolT1))
      val pred = newState.arena.topCell
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.eql(pred.toNameEx, isSubset)))
      newState.setRex(pred.toNameEx)
    }
  }
}
