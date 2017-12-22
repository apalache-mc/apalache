package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper


/**
  * Implements the rules SE-SUBSETEQ[1-3] and SE-SUBSET1.
  *
  * @author Igor Konnov
  */
class SetInclusionRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(state: SymbState): Boolean = {
    state.ex match {
      case OperEx(TlaSetOper.subseteq, _, _) =>
        true

      case OperEx(TlaSetOper.subsetProper, _, _) =>
        true

      case OperEx(TlaSetOper.supseteq, _, _) =>
        true

      case OperEx(TlaSetOper.supsetProper, _, _) =>
        true

      case _ =>
        false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.subseteq, left, right) =>
        // switch to cell theory
        val leftState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(left))
        val leftCell = leftState.arena.findCellByNameEx(leftState.ex)
        val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
        val rightCell = rightState.arena.findCellByNameEx(rightState.ex)
        val finalState: SymbState = (leftCell.cellType, rightCell.cellType) match {
          case (FinSetT(_), FinSetT(_)) =>
            rewriter.lazyEq.subsetEq(rightState, leftCell, rightCell)

          case _ => throw new RewriterException("Unexpected set types: %s and %s in %s"
            .format(leftCell.cellType, rightCell.cellType, state.ex))
        }

        rewriter.coerce(finalState, state.theory)

      case OperEx(TlaSetOper.subsetProper, left, right) =>
        // rewrite as X \subseteq Y /\ ~(Y \subseteq X)
        state.setRex(tla.and(tla.subseteq(left, right), tla.not(tla.subseteq(right, left))))

      case OperEx(TlaSetOper.supseteq, left, right) =>
        apply(state.setRex(tla.subseteq(right, left)))

      case OperEx(TlaSetOper.supsetProper, left, right) =>
        apply(state.setRex(tla.subset(right, left)))

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
