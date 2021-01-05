package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.BoolT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}

/**
  * Implement equality test by delegating the actual test to LazyEquality.
  *
  * @author Igor Konnov
  */
class EqRule(rewriter: SymbStateRewriter) extends RewritingRule {
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

    case OperEx(TlaOper.eq, lhs, rhs) =>
      // Rewrite the both arguments in Cell theory. Although by doing so,
      // we may introduce redundant cells, we don't have to think about types.
      var newState = rewriter.rewriteUntilDone(state.setRex(lhs))
      val leftCell = newState.asCell
      newState = rewriter.rewriteUntilDone(newState.setRex(rhs))
      val rightCell = newState.asCell
      newState = newState.setArena(newState.arena.appendCell(BoolT()))
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
