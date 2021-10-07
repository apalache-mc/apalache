package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.lir.CounterexampleWriter
import at.forsyte.apalache.tla.bmcmt.Checker.{CheckerResult, Deadlock, Error, RuntimeError}
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams.InvariantMode
import at.forsyte.apalache.tla.bmcmt.search.{ModelCheckerParams, SearchState}
import at.forsyte.apalache.tla.bmcmt.trex.{ConstrainedTransitionExecutor, ExecutionSnapshot, TransitionExecutor}
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaFunOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.ReplaceFixed
import at.forsyte.apalache.tla.lir.values.{TlaBool, TlaStr}
import com.typesafe.scalalogging.LazyLogging

/**
 * A new version of the sequential model checker. This version is using TransitionExecutor, which allows us to
 * freely switch between the online and offline SMT solving.
 *
 * @author Igor Konnov
 */
class SeqModelChecker[ExecutorContextT](
    val params: ModelCheckerParams, val checkerInput: CheckerInput, trexImpl: TransitionExecutor[ExecutorContextT]
) extends Checker with LazyLogging {

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
    // apply the Init predicate
    makeStep(isNext = false, checkerInput.initTransitions)
    // unroll the transition relation
    while (searchState.canContinue && trex.stepNo <= params.stepsBound) {
      // apply the Next predicate
      makeStep(isNext = true, checkerInput.nextTransitions)
    }

    if (searchState.nFoundErrors > 0) {
      logger.info("Found %d error(s)".format(searchState.nFoundErrors))
    }

    searchState.finalResult
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
          if (trex.sat(0).contains(true)) {
            val filenames = dumpCounterexample(ValEx(TlaBool(true)))
            val msg = s"Found a deadlock. Check an example state in: ${filenames.mkString(", ")}"
            logger.error(msg)
          } else {
            logger.error(s"Found a deadlock. No SMT model.")
          }
          searchState.onResult(Deadlock())

        case None =>
          searchState.onResult(RuntimeError())
      }
    }

    if (!searchState.canContinue) {
      return
    }

    if (params.invariantMode == InvariantMode.AfterJoin && isNext) {
      checkInvariants(trex.stepNo - 1, notActionInvariants, maybeActionInvariantNos, "action")
      if (!searchState.canContinue) {
        return
      }
    }

    // advance to the next state
    trex.nextState()

    // check the state invariants
    if (params.invariantMode == InvariantMode.AfterJoin) {
      checkInvariants(trex.stepNo - 1, notInvariants, maybeInvariantNos, "state")
      if (!searchState.canContinue) {
        return
      }
    }

    // check the trace invariants
    checkTraceInvariants(trex.stepNo - 1)
  }

  // prepare transitions, check whether they are enabled, and maybe check the invariant (if the user chose so)
  private def prepareTransitionsAndCheckInvariants(
      isNext: Boolean, transitions: Seq[TlaEx]
  ): (Set[Int], Set[Int]) = {
    var maybeInvariantNos: Set[Int] = Set()
    var maybeActionInvariantNos: Set[Int] = Set()

    def addMaybeInvariants(trNo: Int): Set[Int] = {
      val indices = notInvariants.zipWithIndex
        .filter(p => trex.mayChangeAssertion(trNo, p._1))
        .map(_._2)
      val newIndices = indices.toSet
      maybeInvariantNos ++= newIndices
      newIndices
    }

    def addMaybeActionInvariants(trNo: Int): Set[Int] = {
      val indices = notActionInvariants.zipWithIndex
        .filter(p => trex.mayChangeAssertion(trNo, p._1))
        .map(_._2)
      val newIndices = indices.toSet
      maybeActionInvariantNos ++= newIndices
      newIndices
    }

    for ((tr, no) <- transitions.zipWithIndex) {
      var snapshot: Option[SnapshotT] = None
      if (params.discardDisabled) {
        // save the context, unless the transitions are not checked
        snapshot = Some(trex.snapshot())
      }
      val translatedOk = trex.prepareTransition(no, tr)
      if (translatedOk) {
        val transitionInvs = addMaybeInvariants(no)
        val transitionActionInvs = addMaybeActionInvariants(no)

        if (params.discardDisabled) {
          // check, whether the transition is enabled in SMT
          val assumeSnapshot = trex.snapshot()
          // assume that the transition is fired and check, whether the constraints are satisfiable
          trex.assumeTransition(no)
          logger.debug(s"Step ${trex.stepNo}: Transition #$no. Is it enabled?")
          trex.sat(params.smtTimeoutSec) match {
            case Some(true) =>
              logger.debug(s"Step ${trex.stepNo}: Transition #$no is enabled")
              // recover to the state before the transition was fired
              snapshot = Some(assumeSnapshot)

              // keep the transition and collect the invariants
              if (params.invariantMode == InvariantMode.BeforeJoin) {
                // check the action invariants, unless we process Init
                if (isNext) {
                  checkInvariants(trex.stepNo - 1, notActionInvariants, transitionActionInvs, "action")
                  if (!searchState.canContinue) {
                    // an invariant is violated and we cannot continue the search, return immediately
                    return (maybeInvariantNos, maybeActionInvariantNos)
                  }
                }

                // check the state invariants
                trex.nextState() // advance to the next state
                checkInvariants(trex.stepNo - 1, notInvariants, transitionInvs, "state")
                if (!searchState.canContinue) {
                  // an invariant is violated and we cannot continue the search, return immediately
                  return (maybeInvariantNos, maybeActionInvariantNos)
                }
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
          // when --all-enabled is on, the transition has not been assumed
          if (params.invariantMode == InvariantMode.BeforeJoin) {
            if (isNext) {
              checkInvariantsForPreparedTransition(isNext, no, transitionInvs, transitionActionInvs)
            }
            if (!searchState.canContinue) {
              return (Set.empty, Set.empty)
            }
          }
        }
      }
    }

    if (trex.preparedTransitionNumbers.isEmpty) {
      if (trex.sat(0).contains(true)) {
        val filenames = dumpCounterexample(ValEx(TlaBool(true)))
        logger.error(
            s"Found a deadlock. Check the counterexample in: ${filenames.mkString(", ")}"
        )
      } else {
        logger.error(s"Found a deadlock. No SMT model.")
      }
      searchState.onResult(Deadlock())
      (Set.empty, Set.empty)
    } else {
      // pick one transition
      trex.pickTransition()
      (maybeInvariantNos, maybeActionInvariantNos)
    }
  }

  // This is a special case of --all-enabled and search.invariant.mode=before.
  // A transition has been prepared but not assumed.
  private def checkInvariantsForPreparedTransition(
      isNext: Boolean, transitionNo: Int, maybeInvariantNos: Set[Int], maybeActionInvariantNos: Set[Int]
  ): Unit = {
    val snapshot = trex.snapshot()
    // fast track the transition to check the invariants
    trex.assumeTransition(transitionNo)
    if (isNext) {
      // check action invariants
      checkInvariants(trex.stepNo - 1, notActionInvariants, maybeActionInvariantNos, "action")
    }
    if (searchState.canContinue) {
      trex.nextState()
      checkInvariants(trex.stepNo - 1, notInvariants, maybeInvariantNos, "state")
    }
    // and recover
    trex.recover(snapshot)
  }

  // check state invariants or action invariants as indicated by the set of numbers
  private def checkInvariants(
      stateNo: Int, notInvs: Seq[TlaEx], numbersToCheck: Set[Int], kind: String
  ): Unit = {
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
              searchState.onResult(Error(1))
              val filenames = dumpCounterexample(notInv)
              val msg = "State %d: %s invariant %s violated. Check the counterexample in: %s"
                .format(stateNo, kind, invNo, filenames.mkString(", "))
              logger.error(msg)
              excludePathView()

            case Some(false) =>
              // no counterexample found, so the invariant holds true
              invariantHolds = true

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
            searchState.onResult(Error(1))
            val filenames = dumpCounterexample(traceInvApp)
            val msg = "State %d: trace invariant %s violated. Check the counterexample in: %s"
              .format(stateNo, invNo, filenames.mkString(", "))
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
        List(ValEx(TlaStr(key)), value.toNameEx)
      }
      OperEx(TlaFunOper.`enum`, ctorArgs.toList: _*)(Typed(stateType))
    }

    // construct a history sequence
    val seqType = SeqT1(stateType)
    val hist = OperEx(TlaFunOper.tuple, path map mkRecord: _*)(Typed(seqType))
    // assume that the trace invariant is applied to the history sequence
    notTraceInv match {
      case TlaOperDecl(_, List(OperParam(name, 0)), body) =>
        // LET Call_$param == hist IN notTraceInv(param)
        val operType = OperT1(Seq(seqType), BoolT1())
        val callName = s"Call_$name"
        // replace param with $callName() in the body
        val app = OperEx(TlaOper.apply, NameEx(callName)(Typed(operType)))(Typed(seqType))
        val replacedBody = ReplaceFixed(new IdleTracker())({ e => e == NameEx(name)(Typed(seqType)) }, app)(body)
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

          repl(isToReplace, assignedEx.copy())(replacedView)
        }
      // the view over state variables should not be equal to the view over the model values
      val boolTag = Typed(BoolT1())
      OperEx(TlaBoolOper.not, OperEx(TlaOper.eq, modelView, view)(boolTag))(boolTag)
    }

    checkerInput.verificationConditions.stateView.foreach { view =>
      // extract expressions from the model, as we are going to use these expressions (not the cells!) in path constraints
      val exec = trex.decodedExecution()
      // omit the first assignment, as it contains only assignments to the state variables
      val pathConstraint = ValEx(TlaBool(true))(Typed(BoolT1())) :: (exec.path.tail.map(_._1) map computeViewNeq(view))
      trex.addPathOrConstraint(pathConstraint)
    }
  }

  private def dumpCounterexample(notInv: TlaEx): List[String] = {
    val exec = trex.decodedExecution()
    val states = exec.path.map(p => (p._2.toString, p._1))

    def dump(suffix: String): List[String] = {
      CounterexampleWriter.writeAllFormats(
          suffix,
          checkerInput.rootModule,
          notInv,
          states
      )
    }

    // for a human user, write the latest counterexample into counterexample.{tla,json}
    dump("")

    // for automation scripts, produce counterexample${nFoundErrors}.{tla,json}
    dump(searchState.nFoundErrors.toString)
  }
}
