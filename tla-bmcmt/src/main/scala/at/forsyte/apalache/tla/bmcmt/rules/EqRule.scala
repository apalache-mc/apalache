package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, OperEx, Typed}

/**
 * Implement equality test by delegating the actual test to LazyEquality. Integer equality is packed into a single SMT
 * constraint.
 *
 * @author
 *   Igor Konnov, Thomas Pani
 */
class EqRule(rewriter: SymbStateRewriter) extends RewritingRule with IntArithPacker {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaOper.eq, _, _) => true

      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = state.ex match {
    case OperEx(TlaOper.eq, NameEx(left), NameEx(right)) if left == right =>
      // identical constants are obviously equal
      state.setRex(state.arena.cellTrue().toNameEx)

    // Pack integer equality into a single SMT constraint
    case OperEx(TlaOper.eq, lhs, rhs) if lhs.typeTag == Typed(IntT1) && rhs.typeTag == Typed(IntT1) =>
      // pack the arithmetic expression `state.ex` into `packedState.ex`
      val leftState = packArithExpr(rewriter, state.setRex(lhs))
      val rightState = packArithExpr(rewriter, leftState.setRex(rhs))

      // add new arena cell
      val newArena = rightState.arena.appendCell(BoolT1)
      val newCell = newArena.topCell

      // assert the new cell is equal to the packed comparison
      val packedComparison = OperEx(TlaOper.eq, leftState.ex, rightState.ex)
      rewriter.solverContext.assertGroundExpr(tla.eql(newCell.toNameEx, packedComparison))
      // return rewritten state; the input arithmetic expression has been rewritten into the new arena cell
      rightState.setArena(newArena).setRex(newCell.toNameEx)

    case OperEx(TlaOper.eq, lhs, rhs) =>
      var newState = rewriter.rewriteUntilDone(state.setRex(lhs))
      val leftCell = newState.asCell
      newState = rewriter.rewriteUntilDone(newState.setRex(rhs))
      val rightCell = newState.asCell
      newState = newState.setArena(newState.arena.appendCell(BoolT1))
      val eqPred = newState.arena.topCell

      // produce equality constraints, so that we can use SMT equality
      newState = rewriter.lazyEq.cacheOneEqConstraint(newState, leftCell, rightCell)
      // and now we can use the SMT equality
      val eqCons = tla.equiv(eqPred.toNameEx, rewriter.lazyEq.cachedEq(leftCell, rightCell))
      rewriter.solverContext.assertGroundExpr(eqCons)
      newState.setRex(eqPred.toNameEx)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
  }
}
