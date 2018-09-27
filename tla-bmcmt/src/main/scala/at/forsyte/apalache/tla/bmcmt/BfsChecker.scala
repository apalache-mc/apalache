package at.forsyte.apalache.tla.bmcmt

import java.io.{FileWriter, PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FreeExistentialsStore}
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
class BfsChecker(frexStore: FreeExistentialsStore,
                 exprGradeStore: ExprGradeStore,
                 checkerInput: CheckerInput,
                 stepsBound: Int, debug: Boolean = false, profile: Boolean = false) extends Checker with LazyLogging {

  import Checker._

  class CancelSearchException(val outcome: Outcome.Value) extends Exception

  /**
    * A stack of the symbolic states that might constitute a counterexample (the last state is on top).
    */
  private var stack: List[SymbState] = List()
  private val solverContext: SolverContext =
//    new Z3SolverContext(debug)
    new PreproSolverContext(new Z3SolverContext(debug, profile))

  private val rewriter = new SymbStateRewriterImpl(solverContext, exprGradeStore)
  rewriter.freeExistentialsStore = frexStore
  // the checker receives a negation of the invariant at its input, but we need the positive version sometimes
  private var invariant: Option[TlaEx] = None

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
      if (checkerInput.notInvariant.isDefined) {
        // negate notInvariant and simplify it by rewriting
        invariant = Some(new ConstSimplifier().simplify(tla.not(checkerInput.notInvariant.get)))
      }
      var state = makeOneStep(0, dummyState, checkerInput.initTransitions)
      checkInvariant(0, state)
      for (i <- 1 to stepsBound) {
        // checking for deadlocks is not so easy in our encoding
        //        checkForDeadlocks(i, state, nextStates)
        state = makeOneStep(i, state, checkerInput.nextTransitions)
        checkInvariant(i, state)
      }
      Outcome.NoError
    } catch {
      case ce: CancelSearchException =>
        solverContext.dispose() // flushes the log
        ce.outcome
    }
  }

  private def makeOneStep(stepNo: Int, startingState: SymbState, transitions: List[TlaEx]): SymbState = {
    logger.info("Step %d, applying %d transitions".format(stepNo, transitions.length))

    def computeAllEnabled(state: SymbState, ts: List[TlaEx], transitionNo: Int): List[SymbState] =
      ts match {
        case List() =>
          List()

        case tran :: tail =>
          val erased = state.setBinding(forgetPrimed(state.binding))
          val nextState = applyTransition(stepNo, erased, tran, transitionNo)
          rewriter.exprCache.disposeActionLevel() // leave only constants
          if (nextState.isDefined) {
            nextState.get +: computeAllEnabled(nextState.get, tail, transitionNo + 1)
          } else {
            computeAllEnabled(state, tail, transitionNo + 1)
          }
      }

    val nextStates = computeAllEnabled(startingState, transitions, 0)
    if (nextStates.isEmpty) {
      // TODO: explain counterexample
      logger.error(s"No next transition applicable on step $stepNo. Deadlock detected. Check counterexample.")
      dumpCounterexample()
      throw new CancelSearchException(Outcome.RuntimeError)
    } else if (nextStates.lengthCompare(1) == 0) {
      // the only next state -- return it
      val onlyState = nextStates.head
      val resultingState = onlyState.setBinding(shiftBinding(onlyState.binding))
      stack = resultingState +: stack
      resultingState
    } else {
      // pick an index j \in { 0..k } of the fired transition
      val transitionIndex = NameEx(rewriter.solverContext.introIntConst())

      def transitionFired(sAndI: (SymbState, Int)): TlaEx =
        tla.or(tla.neql(transitionIndex, tla.int(sAndI._2)), sAndI._1.ex)

      // the bound on j will be rewritten in pickState
      val leftBound = tla.le(tla.int(0), transitionIndex)
      val rightBound = tla.lt(transitionIndex, tla.int(nextStates.length))
      solverContext.assertGroundExpr(tla.and(nextStates.zipWithIndex.map(transitionFired): _*))

      // glue the computed states S0, ..., Sk together:
      // for every variable x, pick c_x from { S1[x], ..., Sk[x] }
      //   and require \A i \in { 1.. k}. j = i => c_x = Si[x]
      // Then, the final state binds x -> c_x for every x \in Vars
      val lastState = nextStates.last // the last state has the largest arena
      val vars = forgetNonPrimed(lastState.binding).keySet
      val next = lastState.setBinding(forgetPrimed(lastState.binding))
      if (nextStates.map(_.binding).exists(b => forgetNonPrimed(b).keySet != vars)) {
        throw new InternalCheckerError(s"Next states disagree on the set of assigned variables (step $stepNo)")
      }

      def pickVar(x: String): TlaEx = {
        val pickX = tla.in(tla.prime(NameEx(x.stripSuffix("'"))),
          tla.enumSet(nextStates.map(_.binding(x).toNameEx): _*))

        def eq(sAndI: (SymbState, Int)): TlaEx =
          tla.or(tla.neql(transitionIndex, tla.int(sAndI._2)),
            tla.eql(NameEx(x), sAndI._1.binding(x).toNameEx))

        tla.and(pickX +: nextStates.zipWithIndex.map(eq): _*)
      }

      val pickAll = tla.and(leftBound +: rightBound +: vars.toList.map(pickVar): _*)
      val pickState = rewriter.rewriteUntilDone(next.setTheory(BoolTheory()).setRex(pickAll))
      rewriter.solverContext.assertGroundExpr(pickState.ex)
      if (!solverContext.sat()) {
        throw new InternalCheckerError(s"Error picking next variables (step $stepNo). Report a bug.")
      }
      // that is the result of this step
      val resultingState = pickState.setBinding(shiftBinding(pickState.binding))
      stack = resultingState +: stack
      resultingState
    }
  }

  private def applyTransition(stepNo: Int, state: SymbState, transition: TlaEx, transitionNo: Int): Option[SymbState] = {
    rewriter.push()
    logger.debug("Step #%d, transition #%d, SMT context level %d. Applying rewriting rules..."
      .format(stepNo, transitionNo, rewriter.contextLevel))
    solverContext.log("; ------- STEP: %d, STACK LEVEL: %d {".format(stepNo, rewriter.contextLevel))
    val nextState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(transition))
    logger.debug("Finished rewriting. Checking satisfiability of the pushed constraints.")
    if (!solverContext.sat()) {
      // this is a clear sign of a bug in one of the translation rules
      logger.debug("UNSAT after pushing transition constraints")
      throw new CheckerException("A contradiction introduced in rewriting. Report a bug.")
    }
    rewriter.push()
    // assume the constraint constructed by this transition
    solverContext.assertGroundExpr(nextState.ex)
    // check whether this transition violates some assertions
    checkAssertionErrors(nextState)
    logger.debug("Checking satisfiability of the pushed constraints.")
    if (!solverContext.sat()) {
      // the current symbolic state is not feasible
      logger.debug("Transition #%d is not feasible. Skipped.".format(transitionNo))
      rewriter.pop()
      rewriter.pop()
      solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d".format(stepNo, rewriter.contextLevel))
      None
    } else {
      rewriter.pop()
      solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d".format(stepNo, rewriter.contextLevel))
      Some(nextState)
    }
  }

  private def checkAssertionErrors(state: SymbState): Unit = {
    // Detecting runtime errors such as: assertion violation,
    // or function application outside its domain.
    // The crucial assumption here is that IF-THEN-ELSE activates runtime errors only
    // on the active branches, see IfThenElseRule.
    logger.debug("Checking whether the assertions can be violated.")
    rewriter.push()
    val failPreds = state.arena.findCellsByType(FailPredT())
    solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
    if (solverContext.sat()) {
      logger.error("The specification may produce a runtime error. Check the counterexample.")
      val activeFailures =
        failPreds.filter(fp => solverContext.evalGroundExpr(fp.toNameEx) == tla.bool(true))

      logger.error(s"The following failures are possible: %s.".format(activeFailures.mkString(", ")))
      activeFailures.foreach(fp => logger.error(rewriter.findMessage(fp.id)))

      dumpCounterexample()
      // dump everything in the log
      val writer = new StringWriter()
      new SymbStateDecoder(solverContext, rewriter).dumpArena(state, new PrintWriter(writer))
      solverContext.log(writer.getBuffer.toString)

      throw new CancelSearchException(Outcome.RuntimeError)
    }
    rewriter.pop()
    // assume no failure occurs
    solverContext.assertGroundExpr(tla.and(failPreds.map(fp => tla.not(fp.toNameEx)): _*))
  }

  private def checkForDeadlocks(stepNo: Int, state: SymbState, nextStates: List[SymbState]): Unit = {
    rewriter.push()
    solverContext.assertGroundExpr(tla.and(nextStates.map(e => tla.not(e.ex)): _*))
    if (solverContext.sat()) {
      val filename = dumpCounterexample()
      logger.error(s"Deadlock detected at step $stepNo. Check $filename")
      throw new CancelSearchException(Outcome.Deadlock)
    }
    rewriter.pop()
  }

  private def checkInvariant(depth: Int, state: SymbState): Unit = {
    checkAssertionErrors(state)
    if (checkerInput.notInvariant.isDefined) {
      logger.debug("Checking the invariant")
      val notInv = checkerInput.notInvariant.get
      rewriter.push()
      // assert notInv
      val notInvState = rewriter.rewriteUntilDone(state
        .setTheory(BoolTheory())
        .setRex(notInv))
      solverContext.assertGroundExpr(notInvState.ex)
      checkAssertionErrors(notInvState) // the invariant violation may introduce runtime errors
      val notInvSat = solverContext.sat()
      if (notInvSat) {
        val filename = dumpCounterexample()
        logger.error(s"Invariant is violated at depth $depth. Check the counterexample in $filename")
        // dump everything in the log
        val writer = new StringWriter()
        new SymbStateDecoder(solverContext, rewriter).dumpArena(notInvState, new PrintWriter(writer))
        solverContext.log(writer.getBuffer.toString)
        throw new CancelSearchException(Outcome.Error)
      }
      rewriter.pop()
      /*
      // TODO: how useful is the following code?

      rewriter.push()
      val invState = rewriter.rewriteUntilDone(state
        .setTheory(BoolTheory())
        .setRex(invariant.get))
      solverContext.assertGroundExpr(invState.ex)
      val invSat = solverContext.sat()
      if (!invSat) {
        logger.error(s"Invariant is vacuously true at depth $depth.")
        throw new CancelSearchException(Outcome.Error)
      } else {
        // check if the invariant is vacuously true, or if it violates some assertions
        // check whether the invariant violates some assertions
        checkAssertionErrors(invState)
      }
      rewriter.pop()
      */
    }
  }

  private def dumpCounterexample(): String = {
    val filename = "counterexample.txt"
    val writer = new PrintWriter(new FileWriter(filename, false))
    for ((state, i) <- stack.reverse.zipWithIndex) {
      writer.println(s"State $i:")
      writer.println("--------")
      val binding = new SymbStateDecoder(solverContext, rewriter).decodeStateVariables(state)
      for ((name, ex) <- binding) {
        writer.println("%-15s ->  %s".format(name, UTFPrinter.apply(ex)))
      }
      writer.println("========\n")
    }
    writer.close()
    filename
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
