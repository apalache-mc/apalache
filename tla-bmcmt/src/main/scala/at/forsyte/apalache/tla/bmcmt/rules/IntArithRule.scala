package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.types.IntT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

/**
  * Integer arithmetic operations: +, -, *, div, mod.
  *
  * @author Igor Konnov
  */
class IntArithRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val intConstRule: IntConstRule = new IntConstRule(rewriter)
  private val simplifier = new ConstSimplifierForSmt()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.plus, _, _)
           | OperEx(TlaArithOper.minus, _, _)
           | OperEx(TlaArithOper.mult, _, _)
           | OperEx(TlaArithOper.div, _, _)
           | OperEx(TlaArithOper.mod, _, _)
           | OperEx(TlaArithOper.exp, _, _)
           | OperEx(TlaArithOper.uminus, _)
      => true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(oper: TlaArithOper, _, _)
      if (oper == TlaArithOper.plus || oper == TlaArithOper.minus
        || oper == TlaArithOper.mult || oper == TlaArithOper.div
        || oper == TlaArithOper.mod || oper == TlaArithOper.exp)
    =>
      rewriteGeneral(state, state.ex)

    case OperEx(TlaArithOper.uminus, _) =>
      rewriteGeneral(state, state.ex)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  private def rewriteGeneral(state: SymbState, ex: TlaEx) = ex match {
    case ValEx(TlaInt(_)) =>
      // just use the constant rule, which will compare with the integer cache
      intConstRule.apply(state.setRex(ex))

    case OperEx(TlaArithOper.uminus, subex) =>
      val subState = rewriter.rewriteUntilDone(state.setRex(subex))
      // TODO: think how to stop introducing cells for intermediate expressions
      val newArena = subState.arena.appendCell(IntT())
      val newCell = newArena.topCell
      rewriter.solverContext.assertGroundExpr(tla.eql(newCell.toNameEx, tla.uminus(subState.ex)))
      subState.setRex(newCell.toNameEx).setArena(newArena)

    case OperEx(oper: TlaArithOper, left, right) =>
      val leftState = rewriter.rewriteUntilDone(state.setRex(left))
      val rightState = rewriter.rewriteUntilDone(leftState.setRex(right))
      // TODO: think how to stop introducing cells for intermediate expressions
      val newArena = rightState.arena.appendCell(IntT())
      val newCell = newArena.topCell
      // introduce an integer constant to store the result
      val cons = tla.eql(newCell.toNameEx, OperEx(oper, leftState.ex, rightState.ex))
      rewriter.solverContext.assertGroundExpr(cons)
      rightState.setArena(newArena).setRex(newCell.toNameEx)

    case _ =>
      throw new RewriterException("It should not happen. Report a bug", state.ex)
  }
}
