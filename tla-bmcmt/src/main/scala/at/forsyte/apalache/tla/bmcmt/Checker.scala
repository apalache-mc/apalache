package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaModule, TlaOperDecl}

object Checker {

  object Outcome extends Enumeration {
    val NoError, Error, Deadlock = Value
  }

}

/**
  * A bounded model checker using SMT.
  *
  * @author Igor Konnov
  */
class Checker(mod: TlaModule, initOp: TlaOperDecl, nextOp: TlaOperDecl) {
  private var stack: List[Branchpoint] = List()
  private val rewriter = new SymbStateRewriter()

  /**
    * Check all executions of a TLA+ specification up to a bounded number of steps.
    *
    * @param numSteps a bound on the number of steps to explore
    * @return a verification outcome
    */
  def check(numSteps: Int): Outcome.Value = {
    val solverContext = new Z3SolverContext
    val initState = new SymbState(initOp.body, CellTheory(),
      Arena.create(solverContext), new Binding, solverContext)
    // create a dummy branching point, just to have the initial state on the stack
    stack = List(new Branchpoint(initState, 1, initState.solverCtx.level))
    // TODO: use Next, currently we use only Init
    bigStep()
  }

  private def bigStep(): Outcome.Value = {
    val point = stack.head
    if (point.exploredBranchesCnt == point.numBranches) {
      // this branching point is all explored
      stack = stack.tail
      if (stack.isEmpty) {
        // all done
        Outcome.NoError
      } else {
        // roll back to the previous point
        val prevPoint = stack.head
        prevPoint.state.solverCtx.popTo(prevPoint.solverContextLevel)
        bigStep()
      }
    } else {
      // keep exploring the other branches
      val branchNo = point.exploredBranchesCnt
      point.exploredBranchesCnt += 1
      val finalState = smallStep(point.state)
      finalState.ex match {
        case NameEx(name) if CellTheory().hasConst(name) =>
          finalState.solverCtx.assertCellExpr(OperEx(TlaOper.eq, finalState.ex, finalState.arena.cellTrue().toNameEx))

        case _ =>
          throw new CheckerException("Expected a cell, found a TLA expression")
      }

      if (!finalState.solverCtx.sat()) {
        // the current symbolic state is not feasible
        Outcome.Deadlock
      } else {
        // the symbolic state is reachable
        // FIXME: check property
        Outcome.NoError
      }
    }
  }

  private def smallStep(state: SymbState): SymbState = {
    rewriter.rewriteOnce(state) match {
      case Done(nextState) =>
        // converged to the normal form
        nextState

      case Continue(nextState) =>
        // more translation steps are needed
        // TODO: place a guard on the number of recursive calls
        smallStep(nextState)

      case NoRule() =>
        // no rule applies, a problem in the tool?
        throw new RewriterException("No rule applies")
    }
  }

}
