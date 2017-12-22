package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
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
      val finalState = state.setTheory(BoolTheory()).setRex(NameEx(state.solverCtx.trueConst))
      rewriter.coerce(finalState, state.theory)

    case OperEx(TlaOper.eq, le @ NameEx(left), re @ NameEx(right))
        if BoolTheory().hasConst(left) && BoolTheory().hasConst(right)
          || IntTheory().hasConst(left) && IntTheory().hasConst(right)
        =>
      // Boolean and integer equality are easy
      val eqPred = state.solverCtx.introBoolConst()
      state.solverCtx.assertGroundExpr(OperEx(TlaOper.eq, NameEx(eqPred), state.ex))
      val finalState = state.setTheory(BoolTheory()).setRex(NameEx(eqPred))
      rewriter.coerce(finalState, state.theory)

    case OperEx(TlaOper.eq, lhs, rhs) =>
      // Rewrite the both arguments in Cell theory. Although by doing so,
      // we may introduce redundant cells, we don't have to think about types.
      val leftState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(lhs))
      val leftCell = leftState.arena.findCellByNameEx(leftState.ex)
      val rightState = rewriter.rewriteUntilDone(leftState.setTheory(CellTheory()).setRex(rhs))
      val rightCell = rightState.arena.findCellByNameEx(rightState.ex)
      val eqPred = rightState.solverCtx.introBoolConst()

      // produce equality constraints, so that we can use SMT equality
      val eqState = rewriter.lazyEq.cacheOneEqConstraint(rightState, leftCell, rightCell)
      // and now we can use the SMT equality
      val eqCons = tla.equiv(tla.name(eqPred), rewriter.lazyEq.safeEq(leftCell, rightCell))
      rightState.solverCtx.assertGroundExpr(eqCons)
      val finalState = eqState.setRex(NameEx(eqPred))
          .setTheory(BoolTheory()) // we have introduced a Boolean constant
      // coerce to the previous theory, if needed
      rewriter.coerce(finalState, state.theory)

    case _ =>
      throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
  }
}
