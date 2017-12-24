package at.forsyte.apalache.tla.bmcmt

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla

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
class Checker(checkerInput: CheckerInput, stepsBound: Int) {
  private var stack: List[Branchpoint] = List()
  private val solverContext: SolverContext = new Z3SolverContext
  private val rewriter = new SymbStateRewriter(solverContext)

  /**
    * Check all executions of a TLA+ specification up to a bounded number of steps.
    *
    * @return a verification outcome
    */
  def run(): Outcome.Value = {
    // create initial symbolic states
    def mkInitState(transition: TlaEx) = {
      new SymbState(transition, BoolTheory(), Arena.create(solverContext), new Binding)
    }

    // create dummy branching points, just to have the initial states on the stack
    def toBranchpoint(state: SymbState): Branchpoint = new Branchpoint(state, 0, rewriter.contextLevel)

    stack = List(checkerInput.initTransitions.map(mkInitState).map(toBranchpoint): _*)

    // run a depth-first search over symbolic transitions
    dfs()
  }

  private def dfs(): Outcome.Value = {
    val point = stack.head
    stack = stack.tail
    if (point.depth > stepsBound) {
      // we have reached the bound on the number of steps
      if (stack.isEmpty) {
        Outcome.NoError // all done
      } else {
        dfs() // explore the next state
      }
    } else {
      rewriter.pop(rewriter.contextLevel - point.contextLevel) // roll back, if needed
      rewriter.push()
      val nextState = rewriter.rewriteUntilDone(point.state)
      if (!solverContext.sat()) {
        // this is a clear sign of a bug in one of the translation rules
        throw new CheckerException("A contradiction introduced in rewriting. Report a bug.")
      }
      // assume the constraint constructed from Init or Next
      solverContext.assertGroundExpr(nextState.ex)
      if (!solverContext.sat()) {
        // the current symbolic state is not feasible
        Outcome.Deadlock // TODO: actually, it is a deadlock only if all other transitions fail
      } else {
        // the symbolic state is reachable, check the invariant
        if (invariantHolds(nextState)) {
          // construct the next branching points
          stack = constructNextPoints(point, nextState) ++ stack
          // and continue
          dfs()
        } else {
          Outcome.Error
        }
      }
    }
  }

  private def invariantHolds(nextState: SymbState) = {
    if (checkerInput.invariant.isEmpty) {
      true
    } else {
      val inv = checkerInput.invariant.get
      rewriter.push()
      // assert ~Inv' (since we have computed a binding over primed variables)
      val shiftedBinding = shiftBinding(nextState.binding)
      val invState = rewriter.rewriteUntilDone(nextState
        .setTheory(BoolTheory())
        .setRex(inv)
        .setBinding(shiftedBinding))
      solverContext.assertGroundExpr(tla.not(invState.ex))
      val sat = solverContext.sat()
      if (sat) {
        // TODO: explain the counterexample before restoring the SMT context
        // currenly, writing the counterexample in the SMT log
        val writer = new StringWriter()
        new SymbStateDecoder().explainState(solverContext, invState, new PrintWriter(writer))
        solverContext.log(writer.getBuffer.toString)
      }
      rewriter.pop()
      !sat
    }
  }

  // construct next branching points
  private def constructNextPoints(point: Branchpoint, nextState: SymbState): List[Branchpoint] = {
    val shiftedBinding = shiftBinding(nextState.binding)

    def eachTransition(transEx: TlaEx): Branchpoint = {
      new Branchpoint(nextState.setRex(transEx).setBinding(shiftedBinding),
        point.depth + 1, rewriter.contextLevel)
    }

    checkerInput.nextTransitions map eachTransition
  }

  // remove non-primed variables and rename primed variables to non-primed
  private def shiftBinding(binding: Binding): Binding = {
    binding
      .filter(p => p._1.endsWith("'"))
      .map(p => (p._1.stripSuffix("'"), p._2))
  }
}
