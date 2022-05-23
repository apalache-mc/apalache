package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.{BoolT1, OperEx}

/**
 * Integer comparisons: <, <=, >, >=. For equality and inequality, check EqRule.
 *
 * @author
 *   Igor Konnov, Thomas Pani
 */
class IntCmpRule(rewriter: SymbStateRewriter) extends RewritingRule with IntArithPacker {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.lt, _, _) | OperEx(TlaArithOper.le, _, _) | OperEx(TlaArithOper.gt, _, _) |
          OperEx(TlaArithOper.ge, _, _) =>
        true

      // Note that there is no equality, as it is handled by EqRule. Inequality is rewritten by Keramelizer.

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(oper: TlaArithOper, _, _)
        if (oper == TlaArithOper.lt || oper == TlaArithOper.le
          || oper == TlaArithOper.gt || oper == TlaArithOper.ge) =>
      rewritePacked(state)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  private def rewritePacked(state: SymbState) = state.ex match {
    case OperEx(oper, left, right) =>
      // pack the arithmetic expression `state.ex` into `packedState.ex`
      val leftState = packArithExpr(rewriter, state.setRex(left))
      val rightState = packArithExpr(rewriter, leftState.setRex(right))

      // add new arena cell
      val newArena = rightState.arena.appendCell(BoolT1)
      val newCell = newArena.topCell

      // assert the new cell is equal to the packed comparison
      val packedComparison = OperEx(oper, leftState.ex, rightState.ex)
      rewriter.solverContext.assertGroundExpr(tla.eql(newCell.toNameEx, packedComparison))
      // return rewritten state; the input arithmetic expression has been rewritten into the new arena cell
      rightState.setArena(newArena).setRex(newCell.toNameEx)

    case _ =>
      throw new RewriterException("It should not happen. Report a bug", state.ex)
  }

}
