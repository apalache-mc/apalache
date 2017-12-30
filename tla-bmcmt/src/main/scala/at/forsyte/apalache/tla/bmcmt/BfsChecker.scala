package at.forsyte.apalache.tla.bmcmt

import java.io.{PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.analyses.FreeExistentialsStore
import at.forsyte.apalache.tla.bmcmt.types.FailPredT
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import com.typesafe.scalalogging.LazyLogging

/**
  * A bounded model checker using SMT. For each step, this checker applies all possible symbolic transitions
  * and then merges the result. Hence, it is similar to breadth-first search. The major limitation of this search is
  * that for each step, all symbolic transitions should agree on the types of assigned varialbles.
  *
  * @author Igor Konnov
  */
class BfsChecker(frexStore: FreeExistentialsStore, checkerInput: CheckerInput,
                 stepsBound: Int, debug: Boolean = false) extends Checker with LazyLogging {
  import Checker._

  class CancelSearchException(val outcome: Outcome.Value) extends Exception

  /**
    * A stack of the symbolic states in the course of the depth-first search (the last state is on top).
    */
  private var stack: List[SymbState] = List()
  private val solverContext: SolverContext = new Z3SolverContext(debug)
  private val rewriter = new SymbStateRewriter(solverContext)
  rewriter.freeExistentialsStore = frexStore

  /**
    * Check all executions of a TLA+ specification up to a bounded number of steps.
    *
    * @return a verification outcome
    */
  def run(): Outcome.Value = {
    val initialArena = Arena.create(solverContext)
    val dummyState = new SymbState(initialArena.cellTrue().toNameEx,
                                   CellTheory(), initialArena, new Binding)
    try {
      var state = makeOneStep(0, dummyState, checkerInput.initTransitions)
      for (i <- 1 to stepsBound) {
        state = makeOneStep(i, state, checkerInput.nextTransitions)
      }
      Outcome.NoError
    } catch {
      case ce: CancelSearchException =>
        ce.outcome
    }
  }

  private def makeOneStep(stepNo: Int, startingState: SymbState, transitions: List[TlaEx]): SymbState = {
    def computeAllEnabled(state: SymbState, ts: List[TlaEx]): List[SymbState] =
      ts match {
        case List() =>
          List()

        case tran :: tail =>
          val erased = state.setBinding(forgetPrimed(state.binding))
          val nextState = applyTransition(erased, tran)
          if (nextState.isDefined) {
            nextState.get +: computeAllEnabled(nextState.get, tail)
          } else {
            computeAllEnabled(state, tail)
          }
      }

    val nextStates = computeAllEnabled(startingState, transitions)
    if (nextStates.isEmpty) {
      // TODO: explain counterexample
      logger.error(s"No next transition applicable on step $stepNo. Deadlock detected.")
      throw new CancelSearchException(Outcome.RuntimeError)
    } else if (nextStates.lengthCompare(1) == 0) {
      // the only next state -- return it
      val onlyState = nextStates.head
      onlyState.setBinding(shiftBinding(onlyState.binding))
    } else {
      // glue the computed states S0, ..., Sk together:
      // pick an index j \in { 0..k }
      // for every variable x, pick c_x from { S1[x], ..., Sk[x] }
      //   and require \A i \in { 1.. k}. j = i => c_x = Si[x]
      // Then, the final state binds x -> c_x for every x \in Vars
      val lastState = nextStates.last // the last state has the largest arena
      val vars = forgetNonPrimed(lastState.binding).keySet
      val next = lastState.setBinding(forgetPrimed(lastState.binding))
      val selection = NameEx(rewriter.solverContext.introIntConst())
      if (nextStates.map(_.binding).exists(b => forgetNonPrimed(b).keySet != vars)) {
        throw new InternalCheckerError(s"Next states disagree on the set of assigned variables (step $stepNo)")
      }

      def pickVar(x: String): TlaEx = {
        val pickX = tla.in(tla.prime(NameEx(x.stripSuffix("'"))),
                           tla.enumSet(nextStates.map(_.binding(x).toNameEx): _*))

        def eq(sAndI: (SymbState, Int)): TlaEx =
          tla.or(tla.neql(selection, tla.int(sAndI._2)),
                   tla.eql(NameEx(x), sAndI._1.binding(x).toNameEx))

        tla.and(pickX +: nextStates.zipWithIndex.map(eq) :_*)
      }

      val pickAll = tla.and(vars.toList.map(pickVar) :_*)
      val leftBound = tla.le(tla.int(0), selection)
      val rightBound = tla.lt(selection, tla.int(nextStates.length))
      val selectAndPickAll = tla.and(pickAll, leftBound, rightBound)
      val pickState = rewriter.rewriteUntilDone(next.setTheory(BoolTheory()).setRex(selectAndPickAll))
      rewriter.solverContext.assertGroundExpr(pickState.ex)
      if (!solverContext.sat()) {
        throw new InternalCheckerError(s"Error picking next variables (step $stepNo). Report a bug.")
      }
      // that is the result of this step
      pickState.setBinding(shiftBinding(pickState.binding))
    }
  }

  private def applyTransition(state: SymbState, transition: TlaEx): Option[SymbState] = {
    rewriter.push()
    logger.debug("Stack push to level %d, then rewriting".format(rewriter.contextLevel))
    val nextState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(transition))
    logger.debug("Finished rewriting")
    stack = nextState +: stack
    if (!solverContext.sat()) {
      // this is a clear sign of a bug in one of the translation rules
      logger.debug("UNSAT after pushing state constraints")
      throw new CheckerException("A contradiction introduced in rewriting. Report a bug.")
    }
    // assume the constraint constructed by this transition
    solverContext.assertGroundExpr(nextState.ex)
    // check that no failure predicate evaluates to true
    rewriter.push()
    val failPreds = nextState.arena.findCellsByType(FailPredT())
    solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
    if (solverContext.sat()) {
      // TODO: add diagnostic info
      logger.error("The specification may produce a runtime error.")
      throw new CancelSearchException(Outcome.RuntimeError)
    } else {
      rewriter.pop()
      if (!solverContext.sat()) {
        // the current symbolic state is not feasible
        rewriter.pop()
        None
      } else {
        // the symbolic state is reachable, check the invariant
        if (invariantHolds(nextState)) {
          // construct the next branching points
          Some(nextState)
        } else {
          logger.debug("Error found")
          throw new CancelSearchException(Outcome.Error)
        }
      }
    }
  }

  private def invariantHolds(nextState: SymbState) = {
    if (checkerInput.invariant.isEmpty) {
      true
    } else {
      logger.debug("Checking the invariant")
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

  // remove non-primed variables and rename primed variables to non-primed
  private def shiftBinding(binding: Binding): Binding = {
    forgetNonPrimed(binding)
      .map(p => (p._1.stripSuffix("'"), p._2))
  }

  // remove primed variables
  private def forgetPrimed(binding: Binding): Binding = {
    binding.filter(p => !p._1.endsWith("'"))
  }

  // remove primed variables
  private def forgetNonPrimed(binding: Binding): Binding = {
    binding.filter(p => p._1.endsWith("'"))
  }
}
