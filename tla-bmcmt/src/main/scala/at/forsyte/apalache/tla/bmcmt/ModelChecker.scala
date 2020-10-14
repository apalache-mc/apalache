package at.forsyte.apalache.tla.bmcmt

import java.io.{FileWriter, PrintWriter, StringWriter}
import java.util.Calendar

import at.forsyte.apalache.tla.assignments.FalseEx
import at.forsyte.apalache.tla.bmcmt.analyses.{ExprGradeStore, FormulaHintsStore}
import at.forsyte.apalache.tla.bmcmt.rewriter.{ConstSimplifierForSmt, RewriterConfig}
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, MockOracle, Oracle}
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy
import at.forsyte.apalache.tla.bmcmt.search.SearchStrategy._
import at.forsyte.apalache.tla.bmcmt.smt.{SolverContext, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.TlaExUtil
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.io._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaStr}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.immutable.SortedMap
import scala.collection.mutable.ListBuffer

/**
  * A bounded model checker using SMT. The checker itself does not implement a particular search. Instead,
  * it queries a search strategy, e.g., DfsStrategy or BfsStrategy.
  *
  * We expect the invariant to be negated and written over prime variables.
  *
  * @author Igor Konnov
  */
class ModelChecker(typeFinder: TypeFinder[CellT],
                   formulaHintsStore: FormulaHintsStore,
                   changeListener: ChangeListener,
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
  private var stack: List[(SymbState, Oracle)] = List()
  private var typesStack: Seq[SortedMap[String, CellT]] = Seq()
  private val solverContext: SolverContext = new Z3SolverContext(debug, profile)
  // TODO: figure out why the preprocessor slows down invariant checking. Most likely, there is a bug.
  //      new PreproSolverContext(new Z3SolverContext(debug, profile))

  private val rewriter: SymbStateRewriterImpl = new SymbStateRewriterImpl(solverContext, typeFinder, exprGradeStore)
  rewriter.formulaHintsStore = formulaHintsStore
  rewriter.config = RewriterConfig(tuningOptions)

  private val stepFilters: Seq[String] =
    tuningOptions.getOrElse("search.transitionFilter", ".*").split(",")

  private val invFilter: String =
    tuningOptions.getOrElse("search.invariantFilter", "")

  private val invariantSplitByTransition: Boolean =
    tuningOptions.getOrElse("search.invariant.split", "true").toLowerCase == "true"

  private val learnTransFromUnsat: Boolean =
    tuningOptions.getOrElse("search.transition.learnFromUnsat", "").toLowerCase == "true"

  private val learnInvFromUnsat: Boolean =
    tuningOptions.getOrElse("search.invariant.learnFromUnsat", "").toLowerCase == "true"

  private val transitionTimeout: Long =
    BigInt(tuningOptions.getOrElse("search.transition.timeout", "0")).toLong

  private val invariantTimeout: Long =
    BigInt(tuningOptions.getOrElse("search.invariant.timeout", "0")).toLong


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
    val dummyState = new SymbState(initialArena.cellTrue().toNameEx, initialArena, Binding())
    val outcome =
      try {
        val initConstState = initializeConstants(dummyState)
        stack +:= (initConstState, new MockOracle(0))
        typesStack +:= typeFinder.varTypes // the type of CONSTANTS have been computed already
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
          val filenames = dumpCounterexample(ValEx(TlaBool(true)) )
          logger.error(s"Check an execution leading to a deadlock state in any of ${filenames.mkString(", ")}")
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

    val savedVarTypes = rewriter.typeFinder.varTypes // save the variable types before applying the transitions
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
    val simplifier = new ConstSimplifierForSmt()

    def applyTrans(state: SymbState, ts: List[((TlaEx, Int), Boolean)]): List[SymbState] =
      ts match {
        case List() =>
          List(state) // the final state may contain additional cells, add it

        case (tranWithNo, isEnabled) :: tail =>
          if (!isEnabled && !learnTransFromUnsat) {
            applyTrans(state, tail) // ignore the disabled transition, without any rewriting
          } else {
            val (transition, transitionNo) = tranWithNo
            val erased = state.setBinding(forgetPrimed(state.binding))
            // note that the constraints are added at the current level, without an additional push
            var (nextState, _) = applyTransition(stepNo, erased, transition, transitionNo, checkForErrors = false)
            rewriter.exprCache.disposeActionLevel() // leave only the constants
            if (isEnabled && learnInvFromUnsat && invariantSplitByTransition) {
              nextState = assumeInvariant(stepNo, nextState)
            }
            if (isEnabled) {
              // collect the variables of the enabled transition
              nextState +: applyTrans(nextState, tail)
            } else {
              assert(learnTransFromUnsat)
              // Do not collect the variables from the disabled transition, but remember that it was disabled.
              // Note that the constraints are propagated via nextState
              solverContext.assertGroundExpr(simplifier.simplifyShallow(tla.not(nextState.ex)))
              applyTrans(nextState, tail)
            }
          }
      }

    val nextAndLastStates = applyTrans(startingState, transWithEnabled)
    val lastState = nextAndLastStates.last
    val nextStates = nextAndLastStates.slice(0, nextAndLastStates.length - 1)

    val picker = new CherryPick(rewriter)
    // pick an index j \in { 0..k } of the fired transition
    val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(lastState, nextStates.length)

    if (nextStates.isEmpty) {
      throw new IllegalArgumentException("enabled must be non-empty")
    } else if (nextStates.lengthCompare(1) == 0) {
      val resultingState = oracleState.setBinding(shiftBinding(lastState.binding, constants))
      solverContext.assertGroundExpr(lastState.ex)
      if (!invariantSplitByTransition) { checkAllInvariants(stepNo, 0, resultingState) }
      stack +:= (resultingState, oracle) // in this case, oracle is always zero
      shiftTypes(constants)
      typesStack = typeFinder.varTypes +: typesStack
      Some(resultingState)
    } else {
      // if oracle = i, then the ith transition is enabled
      solverContext.assertGroundExpr(oracle.caseAssertions(oracleState, nextStates.map(_.ex)))

      // glue the computed states S_0, ..., S_k together:
      // for every variable x', pick c_x from { S_1[x'], ..., S_k[x'] }
      //   and require \A i \in { 0.. k-1}. j = i => c_x = S_i[x']
      // Then, the final state binds x' -> c_x for every x' \in Vars'
      def getAssignedVars(st: SymbState) = forgetNonPrimed(st.binding, Set()).toMap.keySet

      val primedVars = getAssignedVars(nextStates.head) // only VARIABLES, not CONSTANTS
      var finalState = oracleState
      if (nextStates.exists(getAssignedVars(_) != primedVars)) {
        val index = nextStates.indexWhere(getAssignedVars(_) != primedVars)
        val otherSet = getAssignedVars(nextStates(index))
        val diff = otherSet.union(primedVars).diff(otherSet.intersect(primedVars))
        val msg =
          "[Step %d] Next states 0 and %d disagree on the set of assigned variables: %s"
            .format(stepNo, index, diff.mkString(", "))
        throw new InternalCheckerError(msg, finalState.ex)
      }

      def pickVar(x: String): ArenaCell = {
        val toPickFrom = nextStates map (_.binding(x))
        finalState = picker.pickByOracle(finalState,
          oracle, toPickFrom, finalState.arena.cellFalse().toNameEx) // no else case
        finalState.asCell
      }

      val finalVarBinding = Binding(primedVars.toSeq map (n => (n, pickVar(n))): _*) // variables only
      val constBinding = oracleState.binding.toMap.filter(p => constants.contains(p._1))
      finalState = finalState.setBinding(Binding(finalVarBinding.toMap ++ constBinding))
      if (debug && !solverContext.sat()) {
        throw new InternalCheckerError(s"Error picking next variables (step $stepNo). Report a bug.", finalState.ex)
      }
      // check the invariant, if search invariant.split=false
      if (!invariantSplitByTransition) { checkAllInvariants(stepNo, 0, finalState) }
      if (learnInvFromUnsat && !invariantSplitByTransition) {
        finalState = assumeInvariant(stepNo, finalState)
      }
      // finally, shift the primed variables to non-primed
      finalState = finalState.setBinding(shiftBinding(finalState.binding, constants))
      // that is the result of this step
      stack +:= (finalState, oracle)
      // here we save the transition index, not the oracle, which will be shown to the user
      shiftTypes(constants)
      typesStack = typeFinder.varTypes +: typesStack
      Some(finalState)
    }
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
    var nextState = rewriter.rewriteUntilDone(state.setRex(transition))
    rewriter.flushStatistics()
    if (checkForErrors && debug) {
      // This is a debugging feature that allows us to find incorrect rewriting rules.
      // Disable it in production.
      logger.debug("Finished rewriting. Checking satisfiability of the pushed constraints.")
      solverContext.satOrTimeout(transitionTimeout) match {
        case Some(false) =>
          // this is a clear sign of a bug in one of the translation rules
          logger.debug("UNSAT after pushing transition constraints")
          throw new CheckerException("A contradiction introduced in rewriting. Report a bug.", state.ex)

        case Some(true) => () // SAT
          logger.debug("The transition constraints are OK.")

        case None => // interpret it as sat
          logger.debug("Timeout. Assuming the transition constraints to be OK.")
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
      logger.debug("Checking transition feasibility.")
      solverContext.satOrTimeout(transitionTimeout) match {
        case Some(true) =>
          if (invariantSplitByTransition) {
            // check the invariant as soon as one transition has been applied
            checkAllInvariants(stepNo, transitionNo, nextState)
          }
          // and then forget all these constraints!
          rewriter.pop() // LEVEL + 0
          solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d".format(stepNo, rewriter.contextLevel))
          (nextState, true)
        // LEVEL + 0

        case r: Option[Boolean] => // unsat or timeout
          // the current symbolic state is not feasible
          if (r.isDefined) {
            logger.debug("Transition #%d is not feasible.".format(transitionNo))
          } else {
            logger.debug(s"Timed out when checking feasibility of transition #$transitionNo. Assuming it is infeasible.")
          }
          rewriter.pop() // LEVEL + 0
          solverContext.log("; } ------- STEP: %d, STACK LEVEL: %d TRANSITION: %d"
            .format(stepNo, rewriter.contextLevel, transitionNo))
          (nextState, false)
        // LEVEL + 0
      }
    }
  }

  private def assumeInvariant(stepNo: Int, state: SymbState): SymbState = {
    val matchesInvFilter = invFilter == "" || stepNo.toString.matches("^" + invFilter + "$")
    if (!matchesInvFilter || checkerInput.invariantsAndNegations.isEmpty) {
      state
    } else {
      // as we have checked the invariant, we assume that it holds
      val savedEx = state.ex
      val savedTypes = rewriter.typeFinder.varTypes
      val savedBinding = state.binding
      // rename x' to x, so we are reasoning about the non-primed variables
      shiftTypes(constants)
      var nextState = state.setBinding(shiftBinding(state.binding, constants))

      for (((inv, _), index) <- checkerInput.invariantsAndNegations.zipWithIndex) {
        typeFinder.inferAndSave(inv)
        logger.debug(s"Assuming that the invariant $index holds true")
        nextState = rewriter.rewriteUntilDone(nextState.setRex(inv))
        // assume that the invariant holds true
        solverContext.assertGroundExpr(nextState.ex)
      }

      // restore the expression, the types, and the bindings
      rewriter.typeFinder.reset(savedTypes) // forget about the types that were used to check the invariant
      nextState.setRex(savedEx).setBinding(savedBinding)
    }
  }

  private def checkAllInvariants(stepNo: Int, transitionNo: Int, nextState: SymbState): Unit = {
    val matchesInvFilter = invFilter == "" || stepNo.toString.matches("^" + invFilter + "$")
    if (!matchesInvFilter) {
      return // skip the check if this transition should not be checked
    }

    // if the previous step was filtered, we cannot use the unchanged optimization
    // Bugfix to #108: never filter out the initial step
    val prevMatchesInvFilter =
      stepNo > 0 && (invFilter == "" || (stepNo - 1).toString.matches("^" + invFilter + "$"))

    val invNegs = checkerInput.invariantsAndNegations.map(_._2)
    for ((notInv, invNo) <- invNegs.zipWithIndex) {
      logger.debug(s"Checking the invariant $invNo")
      val changedPrimed =
        if (prevMatchesInvFilter) {
          nextState.changed // only check the invariant if it touches the changed variables
        } else {
          nextState.binding.toMap.keySet // check the invariant in any case, as it could be violated at the previous step
        }
      val savedTypes = rewriter.typeFinder.varTypes
      // rename x' to x, so we are reasoning about the non-primed variables
      shiftTypes(constants)
      val shiftedState = nextState.setBinding(shiftBinding(nextState.binding, constants))
      rewriter.exprCache.disposeActionLevel() // renaming x' to x makes the cache inconsistent, so clean it
      // check the types and the invariant
      checkTypes(notInv)
      checkOneInvariant(stepNo, transitionNo, shiftedState, changedPrimed, notInv)
      rewriter.typeFinder.reset(savedTypes) // forget about the types that were used to check the invariant
    }
  }

  private def checkOneInvariant(stepNo: Int, transitionNo: Int, nextState: SymbState, changedPrimed: Set[String], notInv: TlaEx): Unit = {
    val used = TlaExUtil.findUsedNames(notInv).map(_ + "'") // add primes as the invariant is referring to non-primed variables
    if (used.nonEmpty && used.intersect(changedPrimed).isEmpty) {
      // bugfix for #108: check the invariant over CONSTANTS, if it has not been changed before
      // XXX: it might happen that an invariant over CONSTANTS is checked multiple times. We will fix that in v0.8.0.
      logger.debug(s"The invariant is referring only to the UNCHANGED variables. Skipped.")
    } else {
      rewriter.push()
      val notInvState = rewriter.rewriteUntilDone(nextState
        .setRex(notInv))
      solverContext.assertGroundExpr(notInvState.ex)
      solverContext.satOrTimeout(invariantTimeout) match {
        case Some(true) =>
          // introduce a dummy oracle to hold the transition index, we need it for the counterexample
          val oracle = new MockOracle(transitionNo)
          stack = (notInvState, oracle) +: stack
          val filenames = dumpCounterexample(notInv)
          logger.error(s"Invariant is violated at depth $stepNo. Check the counterexample in any of ${filenames.mkString(", ")}")
          if (debug) {
            logger.warn(s"Dumping the arena into smt.log. This may take some time...")
            // dump everything in the log
            val writer = new StringWriter()
            new SymbStateDecoder(solverContext, rewriter).dumpArena(notInvState, new PrintWriter(writer))
            solverContext.log(writer.getBuffer.toString)
          }
          // cancel the search
          throw new CancelSearchException(Outcome.Error)

        case Some(false) =>
          logger.debug("The invariant holds true.")

        case None =>
          logger.debug("Timeout. Assuming that the invariant holds true.")
      }
      rewriter.pop()
    }
  }

  // returns a list of files with counterexample written
  private def dumpCounterexample(notInv: TlaEx): List[String] = {
    val states = new ListBuffer[NextState]()
    for (((state, oracle), i) <- stack.reverse.zipWithIndex) {
      val decoder = new SymbStateDecoder(solverContext, rewriter)
      val transition = oracle.evalPosition(solverContext, state)
      val binding = decoder.decodeStateVariables(state)
      states += ((transition.toString, binding))
    }
    CounterexampleWriter.writeAllFormats(checkerInput.rootModule, notInv, states.toList)
  }

  private def checkTypes(expr: TlaEx): Unit = {
    typeFinder.inferAndSave(expr)
    if (typeFinder.typeErrors.nonEmpty) {
      def print_error(e: TypeInferenceError): Unit = {
        val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

        val locInfo =
          sourceLocator.sourceOf(e.origin) match {
            case Some(loc) => loc.toString
            case None => "<unknown origin>"
          }
        val exStr = e.origin match {
          case OperEx(op, _*) => op.name + "(...)"
          case ex@_ => ex.toString()
        }
        logger.error("%s, %s, type error: %s".format(locInfo, exStr, e.explanation))
      }

      typeFinder.typeErrors foreach print_error
      throw new CancelSearchException(Outcome.Error)
    }
  }

  /**
    * Remove the non-primed variables (except provided constants)
    * and rename the primed variables to their non-primed versions.
    * After that, remove the type finder to contain the new types only.
    */
  private def shiftTypes(constants: Set[String]): Unit = {
    val types = typeFinder.varTypes
    val nextTypes =
      types.filter(p => p._1.endsWith("'") || constants.contains(p._1))
        .map(p => (p._1.stripSuffix("'"), p._2))
    typeFinder.reset(nextTypes)
  }

  private def forgetPrimedTypes(): Unit = {
    val types = typeFinder.varTypes
    val unprimedTypes = types.filter(!_._1.endsWith("'"))
    typeFinder.reset(unprimedTypes)
  }

  // remove non-primed variables and rename primed variables to non-primed
  private def shiftBinding(binding: Binding, constants: Set[String]): Binding = {
    Binding(forgetNonPrimed(binding, constants).toMap
      .map(p => (p._1.stripSuffix("'"), p._2)))
  }

  // remove primed variables
  private def forgetPrimed(binding: Binding): Binding = {
    Binding(binding.toMap.filter(p => !p._1.endsWith("'")))
  }

  // remove non-primed variables, except the provided constants
  private def forgetNonPrimed(binding: Binding, constants: Set[String]): Binding = {
    Binding(binding.toMap.filter(p => p._1.endsWith("'") || constants.contains(p._1)))
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
    //    def getSourceLocation(ex: TlaEx) = sourceStore.find(ex.ID)
    def getSourceLocation(ex: TlaEx) = {
      val sourceLocator: SourceLocator = SourceLocator(
        sourceStore.makeSourceMap,
        changeListener
      )
      sourceLocator.sourceOf(ex)
    }

    rewriter.getRewritingStack().find(getSourceLocation(_).isDefined) match {
      case None =>
        logger.error("Unable find the source of the problematic expression")

      case Some(ex) =>
        val loc = getSourceLocation(ex).get
        logger.error(s"The problem occurs around the source location $loc")
    }
  }
}
