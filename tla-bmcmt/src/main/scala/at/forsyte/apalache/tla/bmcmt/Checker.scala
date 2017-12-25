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
  /**
    * Unexplored branching points.
    */
  private var unexplored: List[Branchpoint] = List()
  /**
    * A stack of the symbolic states in the course of the depth-first search (the last state is on top).
    */
  private var stack: List[SymbState] = List()
  /**
    * The depth of the last state that was found to be satisfiable
    */
  private var lastSatDepth = -1
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
    val numbers = (checkerInput.initTransitions.length - 1).to(0) by -1 // n-1, ..., 1, 0
    def toBranchpoint(stateAndNo: (SymbState, Int)): Branchpoint =
      new Branchpoint(stateAndNo._1, depth = 0, transitionNo = stateAndNo._2, rewriter.contextLevel)

    unexplored = List(checkerInput.initTransitions.map(mkInitState).zip(numbers).map(toBranchpoint): _*)

    // run a depth-first search over symbolic transitions
    dfs()
  }

  private def dfs(): Outcome.Value = {
    if (unexplored.isEmpty) {
      Outcome.NoError // all done
    } else {
      val point = unexplored.head
      unexplored = unexplored.tail
      if (point.depth > stepsBound) {
        // we have reached the bound on the number of steps
        lastSatDepth = point.depth // unconditionally satisfiable
        dfs() // explore the next state
      } else {
        rewriter.pop(rewriter.contextLevel - point.contextLevel) // roll back, if needed
        stack.drop(stack.length - (1 + point.depth)) // remove the states explored beyond this point
        rewriter.push()
        val nextState = rewriter.rewriteUntilDone(point.state)
        stack = nextState +: stack
        if (!solverContext.sat()) {
          // this is a clear sign of a bug in one of the translation rules
          throw new CheckerException("A contradiction introduced in rewriting. Report a bug.")
        }
        // assume the constraint constructed from Init or Next
        solverContext.assertGroundExpr(nextState.ex)
        if (!solverContext.sat()) {
          // the current symbolic state is not feasible
          if (point.transitionNo == 0 && lastSatDepth <= point.depth) {
            Outcome.Deadlock
          } else {
            // it is not the last transition to explore, continue
            dfs()
          }
        } else {
          lastSatDepth = point.depth // this depth is reached now
          // the symbolic state is reachable, check the invariant
          if (invariantHolds(nextState)) {
            // construct the next branching points
            unexplored = constructNextPoints(point, nextState) ++ unexplored
            // and continue
            dfs()
          } else {
            Outcome.Error
          }
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
    val numbers = (checkerInput.nextTransitions.length - 1).to(0) by -1 // n-1, ..., 1, 0

    def eachTransition(exAndNo: (TlaEx, Int)): Branchpoint = {
      new Branchpoint(nextState.setRex(exAndNo._1).setBinding(shiftedBinding),
        depth = point.depth + 1, transitionNo = exAndNo._2, rewriter.contextLevel)
    }

    checkerInput.nextTransitions.zip(numbers) map eachTransition
  }

  // remove non-primed variables and rename primed variables to non-primed
  private def shiftBinding(binding: Binding): Binding = {
    binding
      .filter(p => p._1.endsWith("'"))
      .map(p => (p._1.stripSuffix("'"), p._2))
  }
}
