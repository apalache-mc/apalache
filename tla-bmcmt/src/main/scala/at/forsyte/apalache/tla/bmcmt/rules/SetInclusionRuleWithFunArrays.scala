package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{CellTFrom, InfSetT, PowSetT}
import at.forsyte.apalache.tla.lir.{OperEx, SetT1}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

class SetInclusionRuleWithFunArrays(rewriter: SymbStateRewriter) extends RewritingRule {

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
        // switch to cell theory
        val leftState = rewriter.rewriteUntilDone(state.setRex(left))
        val leftCell = leftState.asCell
        val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
        val rightCell = rightState.asCell
        (leftCell.cellType, rightCell.cellType) match {
          case (CellTFrom(SetT1(_)), CellTFrom(SetT1(_))) =>
            rewriter.lazyEq.subsetEq(rightState, leftCell, rightCell)

          case (CellTFrom(SetT1(_)), InfSetT(_)) =>
            rewriter.lazyEq.subsetEq(rightState, leftCell, rightCell)

          case (CellTFrom(SetT1(SetT1(t1))), PowSetT(SetT1(t2))) =>
            if (t1 != t2) {
              throw new RewriterException("Unexpected set types: %s and %s in %s"
                    .format(t1, t2, state.ex), state.ex)
            } else {
              subsetInPowset(rightState, leftCell, rightCell)
            }

          case _ =>
            throw new RewriterException("Not implemented (open an issue): %s and %s in %s"
                  .format(leftCell.cellType, rightCell.cellType, state.ex), state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def subsetInPowset(startState: SymbState, leftCell: ArenaCell, rightCell: ArenaCell): SymbState = {
    val powDom = startState.arena.getDom(rightCell)
    def eachElem(state: SymbState, elem: ArenaCell): SymbState = {
      val stateEx = state.ex
      val newState = rewriter.lazyEq.subsetEq(state, elem, powDom)
      val outOrSubsetEq = tla.or(tla.not(tla.apalacheSelectInSet(elem.toNameEx, leftCell.toNameEx)), newState.ex)
      newState.setRex(tla.and(stateEx, outOrSubsetEq))
    }

    startState.arena.getHas(leftCell).foldLeft(startState)(eachElem)
  }
}
