package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter._
import at.forsyte.apalache.tla.lir.{TlaModule, TlaOperDecl}

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
    val initState = new SymbState(TlaRex(initOp.body), Arena.create(), new Binding, new Z3SolverContext)
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
      val finalState = smallStep(point.state, FollowBranch(branchNo))
      finalState.rex match {
        case PredRex(predName) =>
          finalState.solverCtx.assertPred(predName)

        case _ =>
          throw new CheckerException("Expected an SMT predicate, found a TLA expression")
      }

      if (!finalState.solverCtx.isSat()) {
        // the current symbolic state is not feasible
        Outcome.Deadlock
      } else {
        // the symbolic state is reachable
        // FIXME: check property
        Outcome.NoError
      }
    }
  }

  private def smallStep(state: SymbState, dir: SearchDirection): SymbState = {
    rewriter.rewrite(state, dir) match {
      case Done(nextState) =>
        // converged to the normal form
        nextState

      case Continue(nextState) =>
        // more translation steps are needed
        // TODO: place a guard on the number of recursive calls
        smallStep(nextState, FastForward())

      case StateSplit(numBranches) =>
        // create a branching point
        stack = new Branchpoint(state, numBranches, state.solverCtx.level) :: stack
        // and continue with the branch 0
        smallStep(state, FollowBranch(0))

      case NoRule() =>
        // no rule applies, a problem in the tool?
        throw new RewriterException("No rule applies")
    }
  }

}
