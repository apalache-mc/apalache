package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.Checker.Outcome
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.trex.{ExecutionSnapshot, TransitionExecutor}
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
class SeqModelChecker[ExecutorContextT](val params: ModelCheckerParams,
                                        val checkerInput: CheckerInput,
                                        val trex: TransitionExecutor[ExecutorContextT])
    extends Checker with LazyLogging {

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
    val (outcome, maybeInvariantNos) = prepareTransitions(transitions)
    if (outcome != Outcome.NoError) {
      return outcome
    }

    if (!params.pruneDisabled && params.checkForDeadlocks) {
      // We do this check only if all transitions are unconditionally enabled.
      // Otherwise, we should have found it already.
      logger.debug(s"Step %d: checking for deadlocks".format(trex.stepNo))
      trex.sat(params.smtTimeoutSec) match {
        case Some(true) => ()                       // OK

        case Some(false) =>
          if (trex.sat(0).contains(true)) {
            val filenames = dumpCounterexample(ValEx(TlaBool(true)))
            logger.error(s"Found a deadlock. Check the counterexample in: ${filenames.mkString(", ")}")
          } else {
            logger.error(s"Found a deadlock. No SMT model.")
          }
          return Outcome.Deadlock // deadlock

        case None =>
          return Outcome.RuntimeError    // UNKNOWN or timeout
      }
    }

    // advance to the next state
    trex.nextState()

    // check the invariants
    checkInvariants(maybeInvariantNos)
  }

  private def prepareTransitions(transitions: Seq[TlaEx]): (Checker.Outcome.Value, Set[Int]) = {
    var maybeInvariantNos: Set[Int] = Set()

    def addMaybeInvariants(trNo: Int): Unit = {
      val invs = checkerInput.invariantsAndNegations.map(_._1)
      val indices = invs.zipWithIndex.filter(p => trex.mayChangeAssertion(trNo, p._1)).map(_._2)
      maybeInvariantNos ++= indices.toSet
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
          trex.sat(params.smtTimeoutSec) match {
            case Some(true) =>
              addMaybeInvariants(no)          // keep the transition and collect the invariants
              snapshot = Some(assumeSnapshot) // recover to the state before the transition was fired

            case Some(false) =>
              logger.debug(s"Step %d: Transition #%d is disabled".format(trex.stepNo, no))
              ()                              // recover the transition before the transition was prepared

            case None =>
              return (Outcome.RuntimeError, Set.empty) // UNKNOWN or timeout
          }
          // recover from the snapshot
          trex.recover(snapshot.get)
        } else {
          addMaybeInvariants(no)
        }
      }
    }

    if (trex.preparedTransitionNumbers.isEmpty) {
      if (trex.sat(0).contains(true)) {
        val filenames = dumpCounterexample(ValEx(TlaBool(true)))
        logger.error(s"Found a deadlock. Check the counterexample in: ${filenames.mkString(", ")}")
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

  private def checkInvariants(maybeInvariantNos: Set[Int]): Checker.Outcome.Value = {
    // check the invariants
    for (((_, notInv), invNo) <- checkerInput.invariantsAndNegations.zipWithIndex) {
      if (maybeInvariantNos.contains(invNo)) {
        logger.debug(s"Step %d: checking invariant %d".format(trex.stepNo, invNo))
        // save the context
        val snapshot = trex.snapshot()

        // check the invariant
        trex.assertState(notInv)

        trex.sat(params.smtTimeoutSec) match {
          case Some(true) =>
            val filenames = dumpCounterexample(notInv)
            logger.error("Invariant %s violated. Check the counterexample in: %s"
              .format(invNo, filenames.mkString(", ")))
            return Outcome.Error   // the invariant violated

          case Some(false) =>
            ()                    // the invariant holds true

          case None =>
            return Outcome.RuntimeError  // UNKNOWN or timeout
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
    CounterexampleWriter.writeAllFormats(checkerInput.rootModule, notInv, states)
  }
}
