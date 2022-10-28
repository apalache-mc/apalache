package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker._
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams.InvariantMode
import at.forsyte.apalache.tla.bmcmt.search.{ModelCheckerParams, SearchState}
import at.forsyte.apalache.tla.bmcmt.trex.{ConstrainedTransitionExecutor, ExecutionSnapshot, TransitionExecutor}
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.types.tla
import com.typesafe.scalalogging.LazyLogging

import scala.util.Random

/**
 * A new version of the sequential model checker. This version is using TransitionExecutor, which allows us to freely
 * switch between the online and offline SMT solving.
 *
 * @author
 *   Igor Konnov
 */
class SeqModelChecker[ExecutorContextT](
    val params: ModelCheckerParams,
    val checkerInput: CheckerInput,
    trexImpl: TransitionExecutor[ExecutorContextT],
    val listeners: Seq[ModelCheckerListener] = Nil)
    extends Checker with LazyLogging {

  type SnapshotT = ExecutionSnapshot[ExecutorContextT]

  private val trex: ConstrainedTransitionExecutor[ExecutorContextT] =
    new ConstrainedTransitionExecutor[ExecutorContextT](trexImpl)

  private val notInvariants: Seq[TlaEx] = checkerInput.verificationConditions.stateInvariantsAndNegations.map(_._2)
  private val notActionInvariants: Seq[TlaEx] =
    checkerInput.verificationConditions.actionInvariantsAndNegations.map(_._2)
  private val notTraceInvariants: Seq[TlaOperDecl] =
    checkerInput.verificationConditions.traceInvariantsAndNegations.map(_._2)

  // the number of found errors, up to params.maxErrors
  private val searchState: SearchState = new SearchState(params)

  override def run(): CheckerResult = {
    // initialize CONSTANTS
    if (checkerInput.constInitPrimed.isDefined) {
      trex.initializeConstants(checkerInput.constInitPrimed.get)
    }
    // propagate constraints from ASSUME(...)
    checkerInput.rootModule.assumeDeclarations.foreach { d =>
      trex.assertState(d.body)
    }
    val constSnapshot = trex.snapshot()

    // Repeat the search: 1 time in the `check` mode, and `params.nSimulationRuns` times in the `simulation` mode.
    // If the error budget (set with `params.nMaxErrors`) is overrun, terminate immediately.
    while (searchState.canContinue) {
      // apply the Init predicate
      makeStep(isNext = false, checkerInput.initTransitions)
      // unroll the transition relation
      while (searchState.canContinue && trex.stepNo <= params.stepsBound) {
        // apply the Next predicate
        makeStep(isNext = true, checkerInput.nextTransitions)
      }

      if (params.isRandomSimulation && params.saveRuns) {
        outputExampleRun()
      }

      searchState.onRunDone()
      // Continue provided that there are more runs to execute and the error budget is not overrun.
      if (searchState.canContinue) {
        trex.recover(constSnapshot)
        logger.info("----------------------------")
        logger.info(s"Symbolic runs left: ${searchState.nRunsLeft}")
      }
    }

    if (searchState.nFoundErrors > 0) {
      logger.info("Found %d error(s)".format(searchState.nFoundErrors))
    } else if (!params.isRandomSimulation && params.saveRuns) {
      // Output an example in the end of the search.
      outputExampleRun()
    }

    searchState.finalResult
  }

  /**
   * Output an example of the current symbolic run, if the context is satisfiable.
   */
  private def outputExampleRun(): Unit = {
    logger.info("Constructing an example run")
    trex.sat(params.smtTimeoutSec) match {
      case Some(true) =>
        listeners.foreach(_.onExample(checkerInput.rootModule, trex.decodedExecution(), searchState.nRunsLeft))
      case Some(false) =>
        logger.warn("All executions are shorter than the provided bound")
      case None =>
        logger.error("SMT timeout while constructing an example run")
    }
  }

  /**
   * Notify all listeners that a counterexample has been found.
   *
   * @param counterexample
   *   The counterexample to record
   * @param errorIndex
   *   Number of found error (likely [[SearchState.nFoundErrors]]).
   */
  private def notifyOnError(
      counterexample: Counterexample,
      errorIndex: Int): Unit = {
    listeners.foreach(_.onCounterexample(counterexample, errorIndex))
  }

  private def makeStep(isNext: Boolean, transitions: Seq[TlaEx]): Unit = {
    val (maybeInvariantNos, maybeActionInvariantNos) =
      prepareTransitionsAndCheckInvariants(isNext, transitions)
    if (!searchState.canContinue) {
      return
    }

    if (!params.discardDisabled && params.checkForDeadlocks) {
      // We do this check only if all transitions are unconditionally enabled.
      // Otherwise, we should have found it already.
      logger.info(s"Step %d: checking for deadlocks".format(trex.stepNo))
      trex.sat(params.smtTimeoutSec) match {
        case Some(true) => () // OK

        case Some(false) =>
          val counterexample = if (trex.sat(0).contains(true)) {
            val cx = Counterexample(checkerInput.rootModule, trex.decodedExecution(), tla.bool(true))
            notifyOnError(cx, searchState.nFoundErrors)
            logger.error("Found a deadlock.")
            Some(cx)
          } else {
            logger.error(s"Found a deadlock. No SMT model.")
            None
          }
          searchState.onResult(Deadlock(counterexample))

        case None =>
          searchState.onResult(RuntimeError())
      }
    }

    if (!searchState.canContinue) {
      return
    }

    if (params.invariantMode == InvariantMode.AfterJoin && isNext) {
      checkInvariants(trex.stepNo - 1, notActionInvariants, maybeActionInvariantNos, ActionInvariant)
      if (!searchState.canContinue) {
        return
      }
    }

    // advance to the next state
    trex.nextState()

    // check the state invariants
    if (params.invariantMode == InvariantMode.AfterJoin) {
      checkInvariants(trex.stepNo - 1, notInvariants, maybeInvariantNos, StateInvariant)
      if (!searchState.canContinue) {
        return
      }
    }

    // check the trace invariants
    checkTraceInvariants(trex.stepNo - 1)
  }

  // prepare transitions, check whether they are enabled, and maybe check the invariant (if the user chose so)
  private def prepareTransitionsAndCheckInvariants(
      isNext: Boolean,
      transitions: Seq[TlaEx]): (Set[Int], Set[Int]) = {
    var maybeInvariantNos: Set[Int] = Set()
    var maybeActionInvariantNos: Set[Int] = Set()

    def addMaybeInvariants(trNo: Int): Set[Int] = {
      val indices = notInvariants.zipWithIndex
        .filter(p => trex.mayChangeAssertion(trNo, StateInvariant, p._2, p._1))
        .map(_._2)
      val newIndices = indices.toSet
      maybeInvariantNos ++= newIndices
      newIndices
    }

    def addMaybeActionInvariants(trNo: Int): Set[Int] = {
      val indices = notActionInvariants.zipWithIndex
        .filter(p => trex.mayChangeAssertion(trNo, ActionInvariant, p._2, p._1))
        .map(_._2)
      val newIndices = indices.toSet
      maybeActionInvariantNos ++= newIndices
      newIndices
    }

    // in case we do random simulation, shuffle the indices and stop at the first enabled transition
    val transitionIndices =
      if (params.isRandomSimulation) Random.shuffle(transitions.indices.toList) else transitions.indices

    for (no <- transitionIndices) {
      var snapshot: Option[SnapshotT] = None
      if (params.discardDisabled) {
        // save the context, unless the transitions are not checked
        snapshot = Some(trex.snapshot())
      }
      val translatedOk = trex.prepareTransition(no, transitions(no))
      if (translatedOk) {
        val transitionInvs = addMaybeInvariants(no)
        val transitionActionInvs = addMaybeActionInvariants(no)

        if (params.discardDisabled) {
          // check, whether the transition is enabled in SMT
          logger.debug(s"Step ${trex.stepNo}: Transition #$no. Is it enabled?")
          val assumeSnapshot = trex.snapshot()
          // assume that the transition is fired and check, whether the constraints are satisfiable
          trex.assumeTransition(no)
          trex.sat(params.smtTimeoutSec) match {
            case Some(true) =>
              logger.debug(s"Step ${trex.stepNo}: Transition #$no is enabled")
              // recover to the state before the transition was fired
              snapshot = Some(assumeSnapshot)

              // keep the transition and collect the invariants
              if (params.invariantMode == InvariantMode.BeforeJoin) {
                // check the action invariants, unless we process Init
                if (isNext) {
                  checkInvariants(trex.stepNo - 1, notActionInvariants, transitionActionInvs, ActionInvariant)
                  if (!searchState.canContinue) {
                    // an invariant is violated and we cannot continue the search, return immediately
                    return (maybeInvariantNos, maybeActionInvariantNos)
                  }
                }

                // check the state invariants
                trex.nextState() // advance to the next state
                checkInvariants(trex.stepNo - 1, notInvariants, transitionInvs, StateInvariant)
                if (!searchState.canContinue) {
                  // an invariant is violated and we cannot continue the search, return immediately
                  return (maybeInvariantNos, maybeActionInvariantNos)
                }
              }

              if (params.isRandomSimulation) {
                // When random simulation is enabled, we need only one enabled transition.
                // recover from the snapshot
                trex.recover(snapshot.get)
                // pick one transition
                logger.info(s"Step ${trex.stepNo}: randomly picked transition $no")
                trex.pickTransition()
                return (maybeInvariantNos, maybeActionInvariantNos)
              }

            case Some(false) =>
              // recover the transition before the transition was prepared
              logger.info(s"Step ${trex.stepNo}: Transition #$no is disabled")

            case None =>
              searchState.onResult(RuntimeError())
              return (Set.empty, Set.empty) // UNKNOWN or timeout
          }
          // recover from the snapshot
          trex.recover(snapshot.get)
        } else {
          // Special case: when --discard-disabled=false, the transition has not been assumed
          if (params.invariantMode == InvariantMode.BeforeJoin) {
            checkInvariantsForPreparedTransition(isNext, no, transitionInvs, transitionActionInvs)
            if (!searchState.canContinue) {
              return (Set.empty, Set.empty)
            }
          }
        }
      }
    }

    if (trex.preparedTransitionNumbers.isEmpty) {
      if (params.checkForDeadlocks) {
        val counterexample = if (trex.sat(0).contains(true)) {
          val cx = Counterexample(checkerInput.rootModule, trex.decodedExecution(), tla.bool(true))
          notifyOnError(cx, searchState.nFoundErrors)
          logger.error("Found a deadlock.")
          Some(cx)
        } else {
          logger.error(s"Found a deadlock. No SMT model.")
          None
        }
        searchState.onResult(Deadlock(counterexample))
      } else {
        val msg = "All executions are shorter than the provided bound."
        logger.warn(msg)
        searchState.onResult(ExecutionsTooShort())
      }
      (Set.empty, Set.empty)
    } else {
      // pick one transition
      trex.pickTransition()
      (maybeInvariantNos, maybeActionInvariantNos)
    }
  }

  // This is a special case of --discard-disabled=false and search.invariant.mode=before.
  // A transition has been prepared but not assumed.
  private def checkInvariantsForPreparedTransition(
      isNext: Boolean,
      transitionNo: Int,
      maybeInvariantNos: Set[Int],
      maybeActionInvariantNos: Set[Int]): Unit = {
    val snapshot = trex.snapshot()
    // fast track the transition to check the invariants
    trex.assumeTransition(transitionNo)
    if (isNext) {
      // check action invariants
      checkInvariants(trex.stepNo - 1, notActionInvariants, maybeActionInvariantNos, ActionInvariant)
    }
    if (searchState.canContinue) {
      trex.nextState()
      checkInvariants(trex.stepNo - 1, notInvariants, maybeInvariantNos, StateInvariant)
    }
    // and recover
    trex.recover(snapshot)
  }

  // check state invariants or action invariants as indicated by the set of numbers
  private def checkInvariants(
      stateNo: Int,
      notInvs: Seq[TlaEx],
      numbersToCheck: Set[Int],
      kind: InvariantKind): Unit = {
    // check the invariants
    if (numbersToCheck.nonEmpty) {
      logger.info(s"State $stateNo: Checking ${numbersToCheck.size} $kind invariants")
    }

    for ((notInv, invNo) <- notInvs.zipWithIndex) {
      if (numbersToCheck.contains(invNo)) {
        logger.debug(s"State $stateNo: Checking $kind invariant $invNo")
        var invariantHolds = false

        while (!invariantHolds && searchState.canContinue) {
          // save the context
          val snapshot = trex.snapshot()
          // force the new path constraints for the next iteration
          trex.assertPathConstraints()

          // check the invariant
          trex.assertState(notInv)

          trex.sat(params.smtTimeoutSec) match {
            case Some(true) =>
              val counterexample = Counterexample(checkerInput.rootModule, trex.decodedExecution(), notInv)
              searchState.onResult(Error(1, Seq(counterexample)))
              notifyOnError(counterexample, searchState.nFoundErrors)
              logger.info(f"State ${stateNo}: ${kind} invariant ${invNo} violated.")
              excludePathView()

            case Some(false) =>
              // no counterexample found, so the invariant holds true
              invariantHolds = true
              logger.info(f"State ${stateNo}: ${kind} invariant ${invNo} holds.")

            case None =>
              // UNKNOWN or timeout
              searchState.onResult(RuntimeError())
          }

          // rollback the context
          trex.recover(snapshot)
        }
      }
    }
  }

  // check trace invariants
  private def checkTraceInvariants(stateNo: Int): Unit = {
    // check the invariants
    if (notTraceInvariants.nonEmpty) {
      logger.info(s"State $stateNo: Checking ${notTraceInvariants.size} trace invariant(s)")
    }

    for ((notInv, invNo) <- notTraceInvariants.zipWithIndex) {
      logger.debug(s"State $stateNo: Checking trace invariant $invNo")
      var invariantHolds = false

      while (!invariantHolds && searchState.canContinue) {
        // save the context
        val snapshot = trex.snapshot()
        // force the new path constraints for the next iteration
        trex.assertPathConstraints()

        // check the invariant
        val traceInvApp = applyTraceInv(notInv)
        trex.assertState(traceInvApp)

        trex.sat(params.smtTimeoutSec) match {
          case Some(true) =>
            val counterexample = Counterexample(checkerInput.rootModule, trex.decodedExecution(), traceInvApp)
            searchState.onResult(Error(1, Seq(counterexample)))
            notifyOnError(counterexample, searchState.nFoundErrors)
            val msg = "State %d: trace invariant %s violated.".format(stateNo, invNo)
            logger.error(msg)
            excludePathView()

          case Some(false) =>
            // no counterexample found, so the invariant holds true
            invariantHolds = true

          case None =>
            searchState.onResult(RuntimeError())
        }

        // rollback the context
        trex.recover(snapshot)
      }
    }
  }

  private def applyTraceInv(notTraceInv: TlaOperDecl): TlaEx = {
    // the path by transition executor includes the binding before Init, so we apply `tail` to exclude it
    val path = trex.execution.path.map(_._1).tail
    val stateType = RecT1(checkerInput.rootModule.varDeclarations.map(d => d.name -> d.typeTag.asTlaType1()): _*)

    // convert a variable binding to a record
    def mkRecord(b: Binding): TlaEx = {
      val ctorArgs = b.toMap.flatMap { case (key, value) =>
        List(tla.str(key).build, value.toNameEx)
      }
      OperEx(TlaFunOper.rec, ctorArgs.toList: _*)(Typed(stateType))
    }

    // construct a history sequence
    val seqType = SeqT1(stateType)
    val hist = OperEx(TlaFunOper.tuple, path.map(mkRecord): _*)(Typed(seqType))
    // assume that the trace invariant is applied to the history sequence
    notTraceInv match {
      case TlaOperDecl(_, List(OperParam(name, 0)), body) =>
        // LET Call_$param == hist IN notTraceInv(param)
        val operType = OperT1(Seq(seqType), BoolT1)
        val callName = s"Call_$name"
        // replace param with $callName() in the body
        val app = OperEx(TlaOper.apply, NameEx(callName)(Typed(operType)))(Typed(seqType))
        val replacedBody =
          ReplaceFixed(new IdleTracker()).whenMatches({
                _ == NameEx(name)(Typed(seqType))
              }, app)(body)
        LetInEx(replacedBody, TlaOperDecl(callName, List(), hist)(Typed(operType)))

      case TlaOperDecl(name, _, _) =>
        throw new MalformedTlaError(s"Expected a one-argument trace invariant, found: $name", notTraceInv.body)
    }
  }

  // given a satisfiable model, produce a path constraint to exclude the view abstraction of this model
  private def excludePathView(): Unit = {
    def computeViewNeq(view: TlaEx)(assignment: Map[String, TlaEx]): TlaEx = {
      // replace state variables in the view predicate with the expressions that are extracted from the model
      val modelView =
        assignment.foldLeft(view) { case (replacedView, (varName, assignedEx)) =>
          val repl = ReplaceFixed(new IdleTracker())

          def isToReplace: TlaEx => Boolean = {
            case NameEx(name) => name == varName
            case _            => false
          }

          repl.whenMatches(isToReplace, assignedEx.copy())(replacedView)
        }
      // the view over state variables should not be equal to the view over the model values
      val boolTag = Typed(BoolT1)
      OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, modelView, view)(boolTag))(boolTag)
    }

    checkerInput.verificationConditions.stateView.foreach { view =>
      // extract expressions from the model, as we are going to use these expressions (not the cells!) in path constraints
      val exec = trex.decodedExecution()
      // omit the first assignment, as it contains only assignments to the state variables
      val pathConstraint = tla.bool(true).build :: (exec.path.tail.map(_._1).map(computeViewNeq(view)))
      trex.addPathOrConstraint(pathConstraint)
    }
  }
}
