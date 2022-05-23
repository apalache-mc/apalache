package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.{IntT1, OperEx}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaArithOper

/**
 * Integer arithmetic operations: +, -, *, div, mod.
 *
 * @author
 *   Igor Konnov, Thomas Pani
 */
class IntArithRule(rewriter: SymbStateRewriter) extends RewritingRule with IntArithPacker {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaArithOper.plus, _, _) | OperEx(TlaArithOper.minus, _, _) | OperEx(TlaArithOper.mult, _, _) |
          OperEx(TlaArithOper.div, _, _) | OperEx(TlaArithOper.mod, _, _) | OperEx(TlaArithOper.exp, _, _) |
          OperEx(TlaArithOper.uminus, _) =>
        true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(oper: TlaArithOper, _, _)
        if oper == TlaArithOper.plus || oper == TlaArithOper.minus || oper == TlaArithOper.mult ||
          oper == TlaArithOper.div || oper == TlaArithOper.mod || oper == TlaArithOper.exp =>
      rewritePacked(state)

    case OperEx(TlaArithOper.uminus, _) =>
      rewritePacked(state)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }

  /**
   * Rewrite the current arithmetic expression of [[state]], packing it into a single SMT constraint.
   *
   * Essentially, this implements a specialized rewriter of arithmetic expressions within Apalache's more general
   * rewriting system: Arithmetic expressions are packed into a single SMT constraint. If during this rewriting, we
   * encounter a non-arithmetic expression, we delegate the rewriting to [[rewriter]] and substitute the rewritten arena
   * cell in the packed constraint.
   *
   * @param state
   *   current rewriter state, `state.ex` is the arithmetic expression to rewrite
   * @return
   *   rewritten state, where the arithmetic expression has been rewritten into a new arena cell
   */
  private def rewritePacked(state: SymbState): SymbState = {
    // pack the arithmetic expression `state.ex` into `packedState.ex`
    val packedState = packArithExpr(rewriter, state)

    // add new arena cell
    val newArena = packedState.arena.appendCell(IntT1)
    val newCell = newArena.topCell

    // assert the new cell is equal to the packed arithmetic expression
    rewriter.solverContext.assertGroundExpr(tla.eql(newCell.toNameEx, packedState.ex))
    // return rewritten state; the input arithmetic expression has been rewritten into the new arena cell
    packedState.setArena(newArena).setRex(newCell.toNameEx)
  }
}
