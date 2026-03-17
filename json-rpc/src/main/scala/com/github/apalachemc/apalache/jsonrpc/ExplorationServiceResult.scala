package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.databind.JsonNode
import com.fasterxml.jackson.databind.node.NullNode

import scala.collection.immutable.SortedSet

/**
 * All kinds of the results that the exploration service can return.
 */
sealed abstract class ExplorationServiceResult

object AssumptionStatus {
  type T = String
  val ENABLED = "ENABLED"
  val DISABLED = "DISABLED"
  val UNKNOWN = "UNKNOWN"
}

object InvariantStatus {
  type T = String
  val SATISFIED = "SATISFIED"
  val VIOLATED = "VIOLATED"
  val UNKNOWN = "UNKNOWN"
}

object NextModelStatus {
  type T = String
  val TRUE = "TRUE"
  val FALSE = "FALSE"
  val UNKNOWN = "UNKNOWN"
}

/**
 * The result of a health check.
 * @param status
 *   the server status string, typically "OK"
 */
case class HealthCheckResult(status: String) extends ExplorationServiceResult

/**
 * The result of preparing a symbolic transition.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID for recovering the context after the transition has been assumed
 * @param transitionId
 *   the number of the prepared transition
 * @param status
 *   status of the transition: "ENABLED", "DISABLED", or "UNKNOWN"
 */
case class AssumeTransitionResult(
    sessionId: String,
    snapshotId: Int,
    transitionId: Int,
    status: AssumptionStatus.T)
    extends ExplorationServiceResult

/**
 * The result of assuming state constraints.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID for recovering the context after the state has been assumed
 * @param status
 *   status of the assumption: "ENABLED", "DISABLED", or "UNKNOWN"
 */
case class AssumeStateResult(
    sessionId: String,
    snapshotId: Int,
    status: AssumptionStatus.T)
    extends ExplorationServiceResult

/**
 * The result of rolling back to a snapshot.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID that has been recovered
 */
case class RollbackResult(
    sessionId: String,
    snapshotId: Int)
    extends ExplorationServiceResult

/**
 * The result of loading a specification.
 * @param sessionId
 *   the new session ID
 * @param snapshotId
 *   the snapshot ID created right after loading the specification
 * @param specParameters
 *   the specification parameters that are needed for symbolic path exploration
 */
case class LoadSpecResult(sessionId: String, snapshotId: Int, specParameters: SpecParameters)
    extends ExplorationServiceResult

/**
 * Metadata that is attached to actions and invariants.
 * @param index
 *   the index of the action or invariant, starting from 0
 * @param labels
 *   the set of labels attached to the action or invariant
 */
case class SpecEntryMetadata(index: Int, labels: SortedSet[String])

/**
 * Specification parameters that are needed for symbolic path exploration.
 *
 * These entries may differ from what a user expects by reading the specification,
 * as transitions and invariants are decomposed during preprocessing.
 *
 * @param initTransitions
 *   metadata for the initial symbolic transitions
 * @param nextTransitions
 *   metadata for the next-state symbolic transitions
 * @param stateInvariants
 *   metadata for the state invariants
 * @param actionInvariants
 *   metadata for the action invariants
 */
case class SpecParameters(
    initTransitions: Seq[SpecEntryMetadata],
    nextTransitions: Seq[SpecEntryMetadata],
    stateInvariants: Seq[SpecEntryMetadata],
    actionInvariants: Seq[SpecEntryMetadata])

/**
 * The result of disposing a specification.
 * @param sessionId
 *   the ID of the previously loaded specification
 */
case class DisposeSpecResult(sessionId: String) extends ExplorationServiceResult

/**
 * The result of switching to the next step in symbolic path exploration.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID created after taking the next step
 * @param newStepNo
 *   the number of the new step
 */
case class NextStepResult(sessionId: String, snapshotId: Int, newStepNo: Int) extends ExplorationServiceResult

/**
 * The result of checking invariants in the current state or transition.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param invariantStatus
 *   the invariant status: "SATISFIED", "VIOLATED", or "UNKNOWN"
 * @param trace
 *   a JSON-encoded counterexample trace; null when the invariant is not violated
 */
case class CheckInvariantResult(sessionId: String, invariantStatus: InvariantStatus.T, trace: JsonNode)
    extends ExplorationServiceResult

/**
 * The result of querying the current symbolic context.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param trace
 *   a JSON-encoded trace, if it was requested; otherwise null
 * @param operatorValue
 *   a JSON-encoded operator result, if it was requested; otherwise null
 */
case class QueryResult(sessionId: String, trace: JsonNode, operatorValue: JsonNode) extends ExplorationServiceResult

/**
 * The result of finding the next model.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param oldValue
 *   a JSON-encoded value of the operator in the previous model, or null
 * @param hasOld
 *   whether the current context had a model before excluding it
 * @param hasNext
 *   whether a distinct next model was found
 */
case class NextModelResult(
    sessionId: String,
    oldValue: JsonNode,
    hasOld: NextModelStatus.T,
    hasNext: NextModelStatus.T)
    extends ExplorationServiceResult

/**
 * The result of one applyInOrder step.
 * @param ok
 *   true when the step completed successfully
 * @param method
 *   the step method name
 * @param result
 *   the successful method result; null on failure
 * @param error
 *   the step error; null on success
 */
case class ApplyInOrderStepResult(
    ok: Boolean,
    method: String,
    result: JsonNode = NullNode.getInstance(),
    error: JsonNode = NullNode.getInstance())

/**
 * The result of executing a sequence of stateful operations.
 * @param calls
 *   ordered per-call results; execution stops at the first failing call
 */
case class ApplyInOrderResult(calls: Seq[ApplyInOrderStepResult]) extends ExplorationServiceResult
