package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, FinSetT, PowSetT}
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper

class SetInclusionRuleWithArrays(rewriter: SymbStateRewriter) extends SetInclusionRule(rewriter) {
  private val simplifier = new ConstSimplifierForSmt

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.subseteq, left, right) =>
        val leftState = rewriter.rewriteUntilDone(state.setRex(left))
        val leftCell = leftState.arena.findCellByNameEx(leftState.ex)
        val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
        val rightCell = rightState.arena.findCellByNameEx(rightState.ex)
        (leftCell.cellType, rightCell.cellType) match {
          case (FinSetT(_), FinSetT(_)) =>
            subset(rightState, leftCell, rightCell, false)

          case (FinSetT(FinSetT(t1)), PowSetT(FinSetT(t2))) =>
            if (t1 != t2) {
              throw new RewriterException(
                  "Unexpected set types: %s and %s in %s"
                    .format(t1, t2, state.ex), state.ex)
            } else {
              subset(rightState, leftCell, rightCell, true)
            }

          case _ =>
            throw new RewriterException(
                "Unexpected set types: %s and %s in %s"
                  .format(leftCell.cellType, rightCell.cellType, state.ex), state.ex)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def subset(state: SymbState, leftCell: ArenaCell, rightCell: ArenaCell, rightIsPowSet: Boolean): SymbState = {
    var newState = state
    // We check if the elements of leftCell are in rightCell, in order to establish the subset relation
    // If rightCell is a power set, we check if the elements in the sets of leftCell are in the domain of rightCell
    val leftElems =
      if (rightIsPowSet) newState.arena.getHas(leftCell).flatMap(newState.arena.getHas)
      else newState.arena.getHas(leftCell)
    val rightElem = if (rightIsPowSet) newState.arena.getDom(rightCell) else rightCell

    def isInRight(leftElem: ArenaCell): TlaEx = {
      newState = newState.updateArena(_.appendCell(BoolT()))
      val pred = newState.arena.topCell
      rewriter.solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.equiv(pred.toNameEx,
                  tla.in(leftElem.toNameEx, rightElem.toNameEx))))
      pred.toNameEx
    }

    val isSubset = simplifier.simplifyShallow(tla.and(leftElems.map(isInRight): _*))
    newState = newState.updateArena(_.appendCell(BoolT()))
    val pred = newState.arena.topCell
    rewriter.solverContext.assertGroundExpr(tla.eql(pred.toNameEx, isSubset))
    newState.setRex(pred.toNameEx)
  }
}
