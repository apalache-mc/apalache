package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.oper.{TlaArithOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

/**
 * Integer comparisons: <, <=, >, >=. For equality and inequality, check EqRule and NeqRule.
 *
 * @author Igor Konnov
 */
class IntCmpRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val simplifier = new ConstSimplifierForSmt()

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
      rewriteGeneral(state, state.ex)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  private def rewriteGeneral(state: SymbState, ex: TlaEx) = ex match {
    case ValEx(TlaBool(value)) =>
      // keep the simplified expression
      rewriter.rewriteUntilDone(state.setRex(ex))

    case OperEx(oper, left, right) =>
      val leftState = rewriter.rewriteUntilDone(state.setRex(left))
      val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
      // compare integers directly in SMT
      var arena = rightState.arena.appendCell(BoolT())
      val eqPred = arena.topCell
      val cons =
        OperEx(TlaOper.eq, eqPred.toNameEx, OperEx(oper, leftState.ex, rightState.ex))
      rewriter.solverContext.assertGroundExpr(cons)
      rightState.setArena(arena).setRex(eqPred.toNameEx)

    case _ =>
      throw new RewriterException("It should not happen. Report a bug", ex)
  }
}
