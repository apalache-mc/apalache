package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.types.{BoolT, FinSetT}
import at.forsyte.apalache.tla.bmcmt.{RewriterException, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{MalformedTlaError, OperEx}

class EqRuleWithArrays(rewriter: SymbStateRewriter) extends EqRule(rewriter) {
  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(TlaOper.eq, lhs, rhs) =>
      var newState = rewriter.rewriteUntilDone(state.setRex(lhs))
      val leftCell = newState.asCell
      newState = rewriter.rewriteUntilDone(newState.setRex(rhs))
      val rightCell = newState.asCell

      if (!leftCell.cellType.comparableWith(rightCell.cellType)) {
        // Cells of incomparable types cannot be equal.
        // This is a dangerous state, as the type checker should have caught this. Throw an error.
        // It is not really a typing error, but an internal error that should be treated as such.
        val msg =
          "Checking values of incomparable types for equality: %s and %s".format(leftCell.cellType, rightCell.cellType)
        throw new MalformedTlaError(msg, state.ex)
      } else {
        // TODO: add additional elements as development in the "arrays" encoding progresses
        (leftCell.cellType, rightCell.cellType) match {
          case (FinSetT(_), FinSetT(_)) =>
            newState = newState.setArena(newState.arena.appendCell(BoolT()))
            val eqPred = newState.arena.topCell

            // direct SMT equality of arrays is used here
            val eqCons = tla.equiv(eqPred.toNameEx, tla.eql(leftCell.toNameEx, rightCell.toNameEx))
            rewriter.solverContext.assertGroundExpr(eqCons)
            newState.setRex(eqPred.toNameEx)
          case _ =>
            super.apply(state)
        }
      }
    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}
