package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams.InvariantMode
import at.forsyte.apalache.tla.bmcmt.trex.{
  ExecutionSnapshot,
  TransitionExecutor
}
import at.forsyte.apalache.tla.lir.io.CounterexampleWriter
import at.forsyte.apalache.tla.lir.values.TlaBool
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import com.typesafe.scalalogging.LazyLogging

/**
  * A new version of the sequential model checker. This version is using TransitionExecutor, which allows us to
  * freely switch between the online and offline SMT solving.
  *
  * @author Igor Konnov
  */
class SeqModelChecker[ExecutorContextT](
    val params: ModelCheckerParams,
    val checkerInput: CheckerInput,
    val trex: TransitionExecutor[ExecutorContextT]
) extends Checker
    with LazyLogging {

  type SnapshotT = ExecutionSnapshot[ExecutorContextT]

  override def run(): Checker.Outcome.Value = {
    // initialize CONSTANTS
    if (checkerInput.constInitPrimed.isDefined) {
      trex.initializeConstants(checkerInput.constInitPrimed.get)
    }
    // apply the Init predicate
    var outcome = makeStep(checkerInput.initTransitions)
    if (outcome != Outcome.NoError) {
      // report the error immediately
      outcome
    } else {
      // unroll the transition relation
      while (trex.stepNo <= params.stepsBound) {
        // apply the Next predicate
        outcome = makeStep(checkerInput.nextTransitions)
        if (outcome != Outcome.NoError) {
          // report the error immediately
          return outcome
        }
      }
      // else, there is no error
      Outcome.NoError
    }
  }

  private def makeStep(transitions: Seq[TlaEx]): Outcome.Value = {
    val (outcome, maybeInvariantNos) = prepareTransitionsAndCheckInvariants(transitions)
    if (outcome != Outcome.NoError) {
      return outcome
    }

    if (!params.pruneDisabled && params.checkForDeadlocks) {
      // We do this check only if all transitions are unconditionally enabled.
      // Otherwise, we should have found it already.
      logger.info(s"Step %d: checking for deadlocks".format(trex.stepNo))
      trex.sat(params.smtTimeoutSec) match {
        case Some(true) => () // OK

        case Some(false) =>
          if (trex.sat(0).contains(true)) {
            val filenames = dumpCounterexample(ValEx(TlaBool(true)))
            logger.error(
              s"Found a deadlock. Check the counterexample in: ${filenames.mkString(", ")}"
            )
          } else {
            logger.error(s"Found a deadlock. No SMT model.")
          }
          return Outcome.Deadlock // deadlock

        case None =>
          return Outcome.RuntimeError // UNKNOWN or timeout
      }
    }

    // advance to the next state
    trex.nextState()

    // check the invariants
    if (params.invariantMode == InvariantMode.AfterJoin) {
      checkInvariants(trex.stepNo - 1, maybeInvariantNos)
    } else {
      Outcome.NoError
    }
  }

  // prepare transitions, check whether they are enabled, and maybe check the invariant (if the user chose so)
  private def prepareTransitionsAndCheckInvariants(
      transitions: Seq[TlaEx]
  ): (Checker.Outcome.Value, Set[Int]) = {
    var maybeInvariantNos: Set[Int] = Set()

    def addMaybeInvariants(trNo: Int): Set[Int] = {
      val invs = checkerInput.invariantsAndNegations.map(_._1)
      val indices = invs.zipWithIndex
        .filter(p => trex.mayChangeAssertion(trNo, p._1))
        .map(_._2)
      val newIndices = indices.toSet
      maybeInvariantNos ++= newIndices
      newIndices
    }

    for ((tr, no) <- transitions.zipWithIndex) {
      var snapshot: Option[SnapshotT] = None
      if (params.pruneDisabled) {
        // save the context, unless the transitions are not checked
        snapshot = Some(trex.snapshot())
      }
      val translatedOk = trex.prepareTransition(no, tr)
      if (translatedOk) {
        if (params.pruneDisabled) {
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
              val transitionInvs = addMaybeInvariants(no)
              if (params.invariantMode == InvariantMode.BeforeJoin) {
                trex.nextState() // advance to the next state
                val outcome = checkInvariants(trex.stepNo - 1, transitionInvs)
                if (outcome != Outcome.NoError) {
                  // an invariant is violated, return immediately
                  return (outcome, maybeInvariantNos)
                }
              }

            case Some(false) =>
              // recover the transition before the transition was prepared
              logger.info(s"Step ${trex.stepNo}: Transition #$no is disabled")

            case None =>
              return (Outcome.RuntimeError, Set.empty) // UNKNOWN or timeout
          }
          // recover from the snapshot
          trex.recover(snapshot.get)
        } else {
          val transitionInvs = addMaybeInvariants(no)
          if (params.invariantMode == InvariantMode.BeforeJoin) {
            val outcome = checkInvariantsForPreparedTransition(no, transitionInvs)
            if (outcome != Outcome.NoError) {
              // an invariant is violated, return right away
              return (outcome, Set.empty)
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
      (Outcome.Deadlock, Set.empty)
    } else {
      // pick one transition
      trex.pickTransition()
      (Outcome.NoError, maybeInvariantNos)
    }
  }

  // This is a special case of --all-enabled and search.invariant.mode=before.
  // A transition has been prepared but not assumed.
  private def checkInvariantsForPreparedTransition(
      transitionNo: Int,
      maybeInvariantNos: Set[Int]
  ): Checker.Outcome.Value = {
    val snapshot = trex.snapshot()
    // fast track the transition to check the invariants
    trex.assumeTransition(transitionNo)
    trex.nextState()
    val outcome = checkInvariants(trex.stepNo - 1, maybeInvariantNos)
    // and recover
    trex.recover(snapshot)
    outcome
  }

  // check the invariant from a given set
  private def checkInvariants(
      stateNo: Int,
      maybeInvariantNos: Set[Int]
  ): Checker.Outcome.Value = {
    // check the invariants
    if (maybeInvariantNos.nonEmpty) {
      logger.info(s"State $stateNo: Checking ${maybeInvariantNos.size} invariants")
    }

    for (
      ((_, notInv), invNo) <- checkerInput.invariantsAndNegations.zipWithIndex
    ) {
      if (maybeInvariantNos.contains(invNo)) {
        logger.debug(s"State $stateNo: Checking invariant $invNo")
        // save the context
        val snapshot = trex.snapshot()

        // check the invariant
        trex.assertState(notInv)

        trex.sat(params.smtTimeoutSec) match {
          case Some(true) =>
            val filenames = dumpCounterexample(notInv)
            logger.error(
              s"State ${stateNo}: Invariant %s violated. Check the counterexample in: %s"
                .format(invNo, filenames.mkString(", "))
            )
            return Outcome.Error // the invariant violated

          case Some(false) =>
            () // the invariant holds true

          case None =>
            return Outcome.RuntimeError // UNKNOWN or timeout
        }

        // rollback the context
        trex.recover(snapshot)
      }
    }

    Outcome.NoError
  }

  private def dumpCounterexample(notInv: TlaEx): List[String] = {
    val exec = trex.decodedExecution()
    val states = exec.path.map(p => (p._2.toString, p._1))
    CounterexampleWriter.writeAllFormats(
      checkerInput.rootModule,
      notInv,
      states
    )
  }
}
