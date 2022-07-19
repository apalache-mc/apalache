package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.oper.TlaArithOper
import at.forsyte.apalache.tla.lir.values.TlaInt
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, ValEx}

/**
 * Rewrite integer arithmetic expressions, referring to arena cells for non-arithmetic subexpressions as necessary.
 *
 * @author
 *   Thomas Pani
 */
trait IntArithPacker {
  private lazy val substRule = new SubstRule

  /**
   * Rewrite `state`'s expression into an expression that is purely arithmetic, referring to arena cells for
   * non-arithmetic subexpressions.
   *
   * @param rewriter
   *   rewriter to use for non-arithmetic subexpressions
   * @param state
   *   current rewriter state, `state.ex` is the arithmetic expression to rewrite
   * @return
   *   the rewritten state
   */
  protected def packArithExpr(rewriter: SymbStateRewriter, state: SymbState): SymbState = state.ex match {
    /* *** base case: integer literals + names *** */

    // keep integer literals as-is
    case ValEx(TlaInt(_)) => state

    // keep cell names as-is
    case NameEx(name) if ArenaCell.isValidName(name) => state

    // substitute variable names
    case NameEx(_) => substRule(state)

    /* *** recursion: recursively rewrite arithmetic expressions *** */

    case OperEx(TlaArithOper.uminus, subex) =>
      val subState = packArithExpr(rewriter, state.setRex(subex))
      subState.setRex(OperEx(TlaArithOper.uminus, subState.ex))

    case OperEx(oper: TlaArithOper, left, right) =>
      val leftState = packArithExpr(rewriter, state.setRex(left))
      val rightState = packArithExpr(rewriter, leftState.setRex(right))
      rightState.setRex(OperEx(oper, leftState.ex, rightState.ex))

    case ex =>
      // Cannot pack arbitrary expression, delegate to SymbStateRewriter
      rewriter.rewriteUntilDone(state.setRex(ex))
  }
}
