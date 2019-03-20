package at.forsyte.apalache.tla.bmcmt

import java.io.{FileWriter, PrintWriter, StringWriter}

import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FormulaHintsStore, FreeExistentialsStoreImpl}
import at.forsyte.apalache.tla.bmcmt.rules.aux.CherryPick
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.TlaExUtil
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.control.TlaControlOper
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.io.UTFPrinter
import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import com.typesafe.scalalogging.LazyLogging

import scala.collection.immutable.SortedMap

/**
  * A bounded model checker using SMT. The checker itself does not implement a particular search. Instead,
  * it queries a search strategy, e.g., DfsStrategy or BfsStrategy.
  *
  * We expect the invariant to be negated and written over prime variables.
  *
  * @author Igor Konnov
  */
class ModelChecker(typeFinder: TypeFinder[CellT], frexStore: FreeExistentialsStoreImpl,
                   formulaHintsStore: FormulaHintsStore,
                   exprGradeStore: ExprGradeStore, sourceStore: SourceStore, checkerInput: CheckerInput,
                   searchStrategy: SearchStrategy,
                   tuningOptions: Map[String, String],
                   debug: Boolean = false, profile: Boolean = false, checkRuntime: Boolean = false)
  extends Checker with LazyLogging {

  import Checker._

  class CancelSearchException(val outcome: Outcome.Value) extends Exception

  /**
    * A stack of the symbolic states that might constitute a counterexample (the last state is on top).
    */
  private var stack: List[(SymbState, ArenaCell)] = List()
  private var typesStack: Seq[SortedMap[String, CellT]] = Seq()
  private val solverContext: SolverContext =
  //    new Z3SolverContext(debug, profile)
    new PreproSolverContext(new Z3SolverContext(debug, profile))

  private val rewriter: SymbStateRewriterImpl = new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)
  rewriter.freeExistentialsStore = frexStore
  rewriter.formulaHintsStore = formulaHintsStore
  rewriter.introFailures = checkRuntime

  private val stepFilters: Seq[String] =
    tuningOptions.getOrElse("search.transitionFilter", ".*").split(",")

  private val invFilter: String =
    tuningOptions.getOrElse("search.invariantFilter", "")

  private val learnFromUnsat: Boolean =
    tuningOptions.getOrElse("search.learnFromUnsat", "").toLowerCase == "true"


  /**
    * A list of transitions that are enabled at every step
    */
  private var enabledList: Seq[Seq[Int]] = Seq()

  /**
    * A set of CONSTANTS, which are special (rigid) variables, as they do not change in the course of execution.
    */
  private val constants = Set(checkerInput.rootModule.constDeclarations.map(_.name): _*)

  /**
    * Check all executions of a TLA+ specification up to a bounded number of steps.
    *
    * @return a verification outcome
    */
  def run(): Outcome.Value = {
    val initialArena = Arena.create(solverContext)
    val dummyState = new SymbState(initialArena.cellTrue().toNameEx,
      CellTheory(), initialArena, new Binding)
    val outcome =
      try {
        val initConstState = initializeConstants(dummyState)
        stack +:= (initConstState, initialArena.cellTrue())
        typesStack +:= typeFinder.getVarTypes // the type of CONSTANTS have been computed already
        applySearchStrategy()
      } catch {
        case _: CancelSearchException =>
          Outcome.Error

        case err: CheckerException =>
          // try to get any info about the problematic source location
          printRewriterSourceLoc()
          throw err
      }
    // flush the logs
    rewriter.dispose()
    outcome
  }

  /**
    * Use the provided expression to initialize the constants
    *
    * @param state an initial state
    * @return a new state with the constants initialized
    */
  private def initializeConstants(state: SymbState): SymbState = {
    val newState =
      if (checkerInput.constInitPrimed.isEmpty) {
        logger.info("No CONSTANT initializer given")
        state
      } else {
        logger.info("Initializing CONSTANTS with the provided operator")
        checkTypes(checkerInput.constInitPrimed.get)
        val nextState = rewriter.rewriteUntilDone(state.setRex(checkerInput.constInitPrimed.get))
        // importantly, assert the constraints that are imposed by the expression
        rewriter.solverContext.assertGroundExpr(nextState.ex)
        // as the initializer was defined over the primed versions of the constants, shift them back to non-primed
        shiftTypes(Set())
        nextState.setBinding(shiftBinding(nextState.binding, Set()))
      }

    val constants = checkerInput.rootModule.constDeclarations.map(_.name)
    val uninitialized = constants.filter(n => !newState.binding.contains(n))
    if (uninitialized.nonEmpty) {
      logger.error("The following CONSTANTS are not initialized: " + uninitialized.mkString(", "))
      throw new CancelSearchException(Checker.Outcome.RuntimeError)
    }
    newState
  }

  private def applySearchStrategy(): Outcome.Value = {
    searchStrategy.getCommand match {
      case Finish() => Outcome.NoError // done

      case FinishOnDeadlock() =>
        logger.error(s"Deadlock detected.")
        if (solverContext.sat()) {
          logger.error("Check an execution leading to a deadlock state in counterexample.txt")
          dumpCounterexample()
        } else {
          logger.error("No model found that would describe the deadlock")
        }
        Outcome.Deadlock

      case BacktrackOnce() =>
        rewriter.pop()
        logger.debug("Backtracking to level %d".format(rewriter.contextLevel))
        stack = stack.tail
        typesStack = typesStack.tail
        searchStrategy.registerResponse(Backtracked())
        applySearchStrategy()

      case NextStep(stepNo: Int, transitionNos: Seq[Int], popContext: Boolean) =>
        def filter(trs: Seq[TlaEx]): Seq[(TlaEx, Int)] = {
          trs.zipWithIndex filter (p => transitionNos.contains(p._2))
        }

        assert(rewriter.contextLevel == stepNo)
        val (state, _) = stack.head
        val types = typesStack.head
        typeFinder.reset(types) // set the variable type as they should be at this step

        val transitions =
          if (stepNo == 0) filter(checkerInput.initTransitions) else filter(checkerInput.nextTransitions)

        // make the step
        val transWithEnabled = findEnabledOrBugs(stepNo, state, transitions.toList)
        val enabledExists = transWithEnabled.exists(_._2)
        if (!enabledExists) {
          // no push here, as the transition is disabled
          searchStrategy.registerResponse(SearchStrategy.NextStepDisabled())
        } else {
          rewriter.push() // this is needed for backtracking, LEVEL + 1
          val result = applyEnabled(stepNo, state, transWithEnabled)
          assert(result.isDefined)
          searchStrategy.registerResponse(SearchStrategy.NextStepFired())
        }

        applySearchStrategy() // next step
    }
  }

  private def findEnabledOrBugs(stepNo: Int, startingState: SymbState,
                                transitionsAndNos: List[(TlaEx, Int)]): List[((TlaEx, Int), Boolean)] = {
    // find all the feasible transitions and check the invariant for each transition
    logger.info("Step %d, level %d: checking if %d transition(s) are enabled and violate the invariant"
      .format(stepNo, rewriter.contextLevel, transitionsAndNos.length))

    def filterEnabled(state: SymbState, ts: List[(TlaEx, Int)]): List[((TlaEx, Int), Boolean)] = {
      ts match {
        case List() => List()

        case tranWithNo :: tail =>
          val (transition, transitionNo) = tranWithNo
          if (!stepMatchesFilter(stepNo, transitionNo)) {
            filterEnabled(state, tail) // just skip this transition
          } else {
            val erased = state.setBinding(forgetPrimed(state.binding))
            rewriter.push() // LEVEL + 1
            val (nextState, isEnabled) = applyTransition(stepNo, erased, transition, transitionNo, checkForErrors = true)
            rewriter.exprCache.disposeActionLevel() // leave only the constants
            rewriter.pop() // forget all the constraints that were generated by the transition, LEVEL + 0
            (tranWithNo, isEnabled) +: filterEnabled(state, tail)
          }
      }
    }

    val savedVarTypes = rewriter.typeFinder.getVarTypes // save the variable types before applying the transitions
    val enabled = filterEnabled(startingState, transitionsAndNos)
    /*
    enabledList :+= enabled map (_._2) // put it on stack, FIXME: this will not work well with DFS...
    dumpEnabledMap()
    */
    // restore the variable types to apply the enabled transitions once again
    rewriter.typeFinder.reset(savedVarTypes)
    enabled
  }

  private def applyEnabled(stepNo: Int, startingState: SymbState,
                           transWithEnabled: List[((TlaEx, Int), Boolean)]): Option[SymbState] = {
    // second, apply the enabled transitions and collect their effects
    logger.info("Step %d, level %d: collecting %d enabled transition(s)"
      .format(stepNo, rewriter.contextLevel, transWithEnabled.count(_._2)))
    assert(transWithEnabled.nonEmpty)
    val simplifier = new ConstSimplifier()

    def applyTrans(state: SymbState, ts: List[((TlaEx, Int), Boolean)]): List[SymbState] =
      ts match {
        case List() =>
          List(state) // the final state may contain additional cells, add it

        case (tranWithNo, isEnabled) :: tail =>
          if (!isEnabled && !learnFromUnsat) {
            applyTrans(state, tail) // ignore the disabled transition, without any rewriting
          } else {
            val (transition, transitionNo) = tranWithNo
            val erased = state.setBinding(forgetPrimed(state.binding))
            // note that the constraints are added at the current level, without an additional push
            var (nextState, _) = applyTransition(stepNo, erased, transition, transitionNo, checkForErrors = false)
            rewriter.exprCache.disposeActionLevel() // leave only the constants
            if (isEnabled && learnFromUnsat && checkerInput.notInvariant.isDefined) {
              nextState = assumeInvariant(stepNo, nextState)
            }
            if (isEnabled) {
              // collect the variables of the enabled transition
              nextState +: applyTrans(nextState, tail)
            } else {
              assert(learnFromUnsat)
              // Do not collect the variables from the disabled transition, but remember that it was disabled.
              // Note that the constraints are propagated via nextState
              solverContext.assertGroundExpr(simplifier.simplify(tla.not(nextState.ex)))
              applyTrans(nextState, tail)
            }
          }
      }

    val nextAndLastStates = applyTrans(startingState, transWithEnabled)
    val lastState = nextAndLastStates.last
    val nextStates = nextAndLastStates.slice(0, nextAndLastStates.length - 1)

    if (nextStates.isEmpty) {
      throw new IllegalArgumentException("enabled must be non-empty")
    } else if (nextStates.lengthCompare(1) == 0) {
      // The only next state -- return it. Introduce the transition index just for the record.
      val newArena = lastState.arena.appendCell(IntT())
      val transitionIndex = newArena.topCell
      val enabledNo = transWithEnabled.filter(_._2).head._1._2 // the number of the only enabled transition
      solverContext.assertGroundExpr(tla.eql(transitionIndex.toNameEx, tla.int(enabledNo)))
      val resultingState = lastState.setArena(newArena).setBinding(shiftBinding(lastState.binding, constants))
      solverContext.assertGroundExpr(lastState.ex)
      stack +:= (resultingState, transitionIndex)
      shiftTypes(constants)
      typesStack = typeFinder.getVarTypes +: typesStack
      Some(resultingState.setArena(newArena))
    } else {
      // pick an index j \in { 0..k } of the fired transition
      var stateBeforeGluing = lastState // the last state has the largest arena
      stateBeforeGluing = stateBeforeGluing.updateArena(_.appendCell(IntT()))
      val oracle = stateBeforeGluing.arena.topCell  // introduce an oracle to pick the next state
      stateBeforeGluing = mkTransitionIndex(stateBeforeGluing, oracle, transWithEnabled) // and a transition index
      val transitionIndex = stateBeforeGluing.asCell

      def transitionFired(state: SymbState, index: Int): TlaEx =
      // it is tempting to use <=> instead of => here, but this might require from an inactive transition
      // to be completely disabled, while we just say that it is not picked
        tla.impl(tla.eql(oracle.toNameEx, tla.int(index)), state.ex)

      // the bound on j will be rewritten in pickState
      val leftBound = tla.le(tla.int(0), oracle.toNameEx)
      val rightBound = tla.lt(oracle.toNameEx, tla.int(nextStates.length))
      solverContext.assertGroundExpr(tla.and(leftBound, rightBound))
      solverContext.assertGroundExpr(tla.and(nextStates.zipWithIndex.map((transitionFired _).tupled): _*))

      // glue the computed states S0, ..., Sk together:
      // for every variable x, pick c_x from { S1[x], ..., Sk[x] }
      //   and require \A i \in { 0.. k-1}. j = i => c_x = Si[x]
      // Then, the final state binds x -> c_x for every x \in Vars
      val vars = forgetNonPrimed(nextStates.head.binding, Set()).keySet // only VARIABLES, not CONSTANTS
      var finalState = stateBeforeGluing.setBinding(forgetPrimed(stateBeforeGluing.binding)).setRex(tla.bool(true))
      if (nextStates.map(_.binding).exists(b => forgetNonPrimed(b, Set()).keySet != vars)) {
        throw new InternalCheckerError(s"Next states disagree on the set of assigned variables (step $stepNo)")
      }

      def pickVar(x: String): ArenaCell = {
        val toPickFrom = nextStates map (_.binding(x))
        finalState = new CherryPick(rewriter).pickByOracle(finalState, oracle.toNameEx, toPickFrom)
        finalState.asCell
      }

      val finalVarBinding = Binding(vars.toSeq map (n => (n, pickVar(n))): _*) // variables only
      val constBinding = stateBeforeGluing.binding.filter(p => constants.contains(p._1))
      val finalBinding = Binding(shiftBinding(finalVarBinding, Set()) ++ constBinding) // recover constants
      finalState = finalState.setBinding(finalBinding)
      if (!solverContext.sat()) {
        throw new InternalCheckerError(s"Error picking next variables (step $stepNo). Report a bug.")
      }
      // that is the result of this step
      stack +:= (finalState, transitionIndex)
        // here we save the transition index, not the oracle, which will be shown to the user
      shiftTypes(constants)
      typesStack = typeFinder.getVarTypes +: typesStack
      Some(finalState)
    }
  }

  // Introduce a transition index for an oracle. The problem is that the oracles ranges over the indices of
  // the enabled transitions, while the users want to see the indices from the range of all transitions.
  private def mkTransitionIndex(state: SymbState, oracle: ArenaCell,
                                transWithEnabled: List[((TlaEx, Int), Boolean)]): SymbState = {
    val newArena = state.arena.appendCell(IntT())
    val transitionIndex = newArena.topCell // it is also the oracle for picking cells
    val enabled = transWithEnabled.filter(_._2).map(_._1._2) // keep the enabled numbers only
    for ((no, i) <- enabled.zipWithIndex) {
      solverContext.assertGroundExpr(tla.impl(tla.eql(oracle.toNameEx, tla.int(i)),
                                              tla.eql(transitionIndex.toNameEx, tla.int(no))))
    }
    state.setArena(newArena).setRex(transitionIndex.toNameEx)
  }

  // This method adds constraints right in the current context, without doing push
  private def applyTransition(stepNo: Int, state: SymbState, transition: TlaEx,
                              transitionNo: Int, checkForErrors: Boolean): (SymbState, Boolean) = {
    logger.debug("Step #%d, transition #%d, SMT context level %d."
      .format(stepNo, transitionNo, rewriter.contextLevel))
    logger.debug("Finding types of the variables...")
    checkTypes(transition)
    solverContext.log("; ------- STEP: %d, STACK LEVEL: %d TRANSITION: %d {"
      .format(stepNo, rewriter.contextLevel, transitionNo))
    logger.debug("Applying rewriting rules...")
    var nextState = rewriter.rewriteUntilDone(state.setTheory(BoolTheory()).setRex(transition))
    rewriter.flushStatistics()
    if (checkForErrors) {
      logger.debug("Finished rewriting. Checking satisfiability of the pushed constraints.")
      if (!solverContext.sat()) {
        // this is a clear sign of a bug in one of the translation rules
        logger.debug("UNSAT after pushing transition constraints")
        throw new CheckerException("A contradiction introduced in rewriting. Report a bug.")
      }
    }
    if (!checkForErrors) {
      // this was an experimental feature, which did not work nicely
      // assume no failure occurs
      //      val failPreds = state.arena.findCellsByType(FailPredT())
      //      failPreds.map(fp => tla.not(fp.toNameEx)) foreach solverContext.assertGroundExpr
      // just return the state
      (nextState, true)
      // LEVEL + 0
    } else {
      rewriter.push() // LEVEL + 1
      // assume the constraint constructed by this transition
      solverContext.assertGroundExpr(nextState.ex)
      // check whether this transition violates some assertions
      checkAssertionErrors(nextState)
      logger.debug("Checking transition feasibility.")
      if (!solverContext.sat()) {
        // the current symbolic state is not feasible
        logger.debug("Transition #%d is not feasible.".format(transitionNo))
        rewriter.pop() // LEVEL + 0
        solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d TRANSITION: %d"
          .format(stepNo, rewriter.contextLevel, transitionNo))
        (nextState, false)
        // LEVEL + 0
      } else {
        // check the invariant right here
        val matchesInvFilter = invFilter == "" || stepNo.toString.matches("^" + invFilter + "$")
        if (matchesInvFilter) {
          checkInvariant(stepNo, nextState)
        }
        // and then forget all these constraints!
        rewriter.pop() // LEVEL + 0
        solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d".format(stepNo, rewriter.contextLevel))
        (nextState, true)
        // LEVEL + 0
      }
    }
  }

  private def assumeInvariant(stepNo: Int, state: SymbState): SymbState = {
    val matchesInvFilter = invFilter == "" || stepNo.toString.matches("^" + invFilter + "$")
    if (!matchesInvFilter || checkerInput.notInvariant.isEmpty) {
      state
    } else {
      // as we have checked the invariant, we assume that it holds
      logger.debug("Assuming that the invariant holds")
      val prevEx = state.ex
      val simplifier = new ConstSimplifier()
      val nextState = rewriter.rewriteUntilDone(state.setRex(simplifier.simplify(tla.not(checkerInput.notInvariant.get))))
      solverContext.assertGroundExpr(nextState.ex)
      nextState.setRex(prevEx) // restore the expression
    }
  }

  private def checkAssertionErrors(state: SymbState): Unit = {
    // FIXME: this mechanism is broken in unstable, as the rules are not producing failure predicates anymore
    // Detecting runtime errors such as: assertion violation,
    // or function application outside its domain.
    // The crucial assumption here is that IF-THEN-ELSE activates runtime errors only
    // on the active branches, see IfThenElseRule.
    val failPreds = state.arena.findCellsByType(FailPredT())
    if (checkRuntime) {
      logger.debug("Checking for runtime errors")
      rewriter.push()
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
      logger.debug("No runtime errors")
    }
    // assume no failure occurs
    failPreds.map(fp => tla.not(fp.toNameEx)) foreach solverContext.assertGroundExpr
  }

  // TODO: This decomposition could be done at previous phases
  private def checkInvariantPiecewise(depth: Int, nextState: SymbState, changed: Set[String], notInv: TlaEx): Boolean = {
    // check the disjuncts separately, in order to simplify the problem for SMT
    notInv match {
      case OperEx(TlaBoolOper.or, args@_*) =>
        args exists (a => checkInvariantPiecewise(depth, nextState, changed, a))

      case OperEx(TlaBoolOper.exists, name, set, OperEx(TlaBoolOper.or, args@_*)) =>
        def oneExists(a: TlaEx) = {
          // this existential can be skolemized
          val ex = tla.exists(name, set, a)
          frexStore.store.add(ex.ID)
          ex
        }
        // use the equivalence \E x \in S: A \/ B <=> (\E x \in S: A) \/ (\E x \in S: B)
        args exists (a => checkInvariantPiecewise(depth, nextState, changed, oneExists(a)))

      case ite@OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx) =>
        // ITE(A, B, C) == A /\ B \/ ~A /\ B
        val pieces = Seq(tla.and(predEx, thenEx), tla.and(tla.not(predEx), elseEx))
        pieces exists (a => checkInvariantPiecewise(depth, nextState, changed, a))

      case OperEx(TlaBoolOper.exists, name, set, OperEx(TlaControlOper.ifThenElse, predEx, thenEx, elseEx)) =>
        // \E x \in S: ITE(A, B, C) == (\E x \in S: A /\ B) \/ (\E x \in S: ~A /\ B)
        def oneExists(a: TlaEx) = {
          // this existential can be skolemized
          val ex = tla.exists(name, set, a)
          frexStore.store.add(ex.ID)
          ex
        }

        val pieces = Seq(oneExists(tla.and(predEx, thenEx)), oneExists(tla.and(tla.not(predEx), elseEx)))
        // use the equivalence \E x \in S: A \/ B <=> (\E x \in S: A) \/ (\E x \in S: B)
        pieces exists (a => checkInvariantPiecewise(depth, nextState, changed, oneExists(a)))

      case _ =>
        logger.debug(s"Checking an invariant piece $notInv")
        val used = TlaExUtil.findUsedNames(notInv)
        if (used.intersect(changed).isEmpty) {
          logger.debug(s"The invariant is referring only to the UNCHANGED variables. Skipped.")
          false
        } else {
          rewriter.push()
          val notInvState = rewriter.rewriteUntilDone(nextState
            .setTheory(BoolTheory())
            .setRex(notInv))
          solverContext.assertGroundExpr(notInvState.ex)
          checkAssertionErrors(notInvState) // the invariant violation may introduce runtime errors
          val notInvSat = solverContext.sat()
          if (notInvSat) {
            val newArena = notInvState.arena.appendCell(IntT()) // FIXME
            val transitionIndex = newArena.topCell

            val finalState = notInvState.setArena(newArena).setBinding(shiftBinding(notInvState.binding, constants))
            stack = (finalState, transitionIndex) +: stack
            val filename = dumpCounterexample()
            logger.error(s"Invariant is violated at depth $depth. Check the counterexample in $filename")
            if (debug) {
              logger.warn(s"Dumping the arena into smt.log. This may take some time...")
              // dump everything in the log
              val writer = new StringWriter()
              new SymbStateDecoder(solverContext, rewriter).dumpArena(notInvState, new PrintWriter(writer))
              solverContext.log(writer.getBuffer.toString)
            }
            throw new CancelSearchException(Outcome.Error)
          }
          rewriter.pop()
          notInvSat
        }
    }
  }

  private def checkInvariant(depth: Int, nextState: SymbState): SymbState = {
    checkAssertionErrors(nextState)

    if (checkerInput.notInvariant.isEmpty) {
      nextState
    } else {
      logger.debug("Checking the invariant")
      val notInv = checkerInput.notInvariant.get
      val savedTypes = rewriter.typeFinder.getVarTypes
      checkTypes(notInv)
      val changed = nextState.changed
      val notInvSat = checkInvariantPiecewise(depth, nextState, changed, notInv)
      rewriter.typeFinder.reset(savedTypes) // forget about the types that were used to check the invariant
      nextState
    }
  }

  private def dumpCounterexample(): String = {
    val filename = "counterexample.txt"
    val writer = new PrintWriter(new FileWriter(filename, false))
    for (((state, transitionCell), i) <- stack.reverse.zipWithIndex) {
      val decoder = new SymbStateDecoder(solverContext, rewriter)
      val transition = decoder.decodeCellToTlaEx(state.arena, transitionCell)
      writer.println(s"State $i (from transition $transition):")
      writer.println("--------")
      val binding = decoder.decodeStateVariables(state)
      for (name <- binding.keys.toSeq.sorted) { // sort the keys
        writer.println("%-15s ->  %s".format(name, UTFPrinter.apply(binding(name))))
      }
      writer.println("========\n")
    }
    writer.close()
    filename
  }

  private def checkTypes(expr: TlaEx): Unit = {
    typeFinder.inferAndSave(expr)
    if (typeFinder.getTypeErrors.nonEmpty) {
      def print_error(e: TypeInferenceError): Unit = {
        val locInfo =
          sourceStore.find(e.origin.safeId) match {
            case Some(loc) => loc.toString
            case None => "<unknown origin>"
          }
        val exStr = e.origin match {
          case OperEx(op, _*) => op.name + "(...)"
          case ex@_ => ex.toString()
        }
        logger.error("%s, %s, type error: %s".format(locInfo, exStr, e.explanation))
      }

      typeFinder.getTypeErrors foreach print_error
      throw new CancelSearchException(Outcome.Error)
    }
  }

  /**
    * Remove the non-primed variables (except provided constants)
    * and rename the primed variables to their non-primed versions.
    * After that, remove the type finder to contain the new types only.
    */
  private def shiftTypes(constants: Set[String]): Unit = {
    val types = typeFinder.getVarTypes
    val nextTypes =
      types.filter(p => p._1.endsWith("'") || constants.contains(p._1))
        .map(p => (p._1.stripSuffix("'"), p._2))
    typeFinder.reset(nextTypes)
  }

  private def forgetPrimedTypes(): Unit = {
    val types = typeFinder.getVarTypes
    val unprimedTypes = types.filter(!_._1.endsWith("'"))
    typeFinder.reset(unprimedTypes)
  }

  // remove non-primed variables and rename primed variables to non-primed
  private def shiftBinding(binding: Binding, constants: Set[String]): Binding = {
    forgetNonPrimed(binding, constants)
      .map(p => (p._1.stripSuffix("'"), p._2))
  }

  // remove primed variables
  private def forgetPrimed(binding: Binding): Binding = {
    binding.filter(p => !p._1.endsWith("'"))
  }

  // remove non-primed variables, except the provided constants
  private def forgetNonPrimed(binding: Binding, constants: Set[String]): Binding = {
    binding.filter(p => p._1.endsWith("'") || constants.contains(p._1))
  }

  // does the transition number satisfy the given filter at the given step?
  private def stepMatchesFilter(stepNo: Int, transitionNo: Int): Boolean = {
    if (stepFilters.size <= stepNo) {
      true // no filter applied
    } else {
      transitionNo.toString.matches("^%s$".format(stepFilters(stepNo)))
    }
  }

  private def dumpEnabledMap(): Unit = {
    val filename = "enabled-map.txt"
    val writer = new PrintWriter(new FileWriter(filename, false))
    val transitionsCnt = checkerInput.nextTransitions.size
    writer.println("The map of enabled transitions:")
    val hrule = "----%s".format((0 until transitionsCnt map (_ => "-")) mkString "")
    writer.println(hrule)
    writer.println("    %s".format(0 until transitionsCnt map (i => ((i / 100) % 10).toString) mkString ""))
    writer.println("    %s".format(0 until transitionsCnt map (i => ((i / 10) % 10).toString) mkString ""))
    writer.println("    %s".format(0 until transitionsCnt map (i => (i % 10).toString) mkString ""))
    writer.println(hrule)
    for ((enabled, stepNo) <- enabledList.zipWithIndex) {
      val set = Set(enabled: _*)
      val line = 0 until transitionsCnt map (i => if (set.contains(i)) "*" else " ") mkString ""
      writer.println(s"%3d:%s".format(stepNo, line))
    }
    writer.println(hrule)
    writer.close()
  }

  private def printRewriterSourceLoc(): Unit = {
    def getSourceLocation(ex: TlaEx) = sourceStore.find(ex.ID)

    rewriter.getRewritingStack().find(getSourceLocation(_).isDefined) match {
      case None =>
        logger.error("Unable find the source of the problematic expression")

      case Some(ex) =>
        val loc = getSourceLocation(ex).get
        logger.error(s"The problem occurs around the source location $loc")
    }
  }
}
