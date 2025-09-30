package com.github.apalachemc.apalache.jsonrpc

import com.fasterxml.jackson.databind.JsonNode

/**
 * All kinds of the results that the exploration service can return.
 */
sealed abstract class ExplorationServiceResult

object TransitionStatus {
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
  val TIMEOUT = "TIMEOUT"
}

/**
 * The result of preparing a symbolic transition.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param snapshotId
 *   the snapshot ID for recovering the context after the transition has been assumed.
 * @param transitionId
 *   the number of the prepared transition
 * @param status
 *   status of the transition: "ENABLED", "DISABLED", or "UNKNOWN"
 */
case class AssumeTransitionResult(
    sessionId: String,
    snapshotId: Int,
    transitionId: Int,
    status: TransitionStatus.T)
    extends ExplorationServiceResult

/**
 * The result of loading a specification.
 * @param sessionId
 *   the new session ID
 * @param snapshotId
 *   the snapshot ID for recovering the context right after loading the specification.
 * @param specParameters
 *   the specification parameters that are needed for symbolic path exploration
 */
case class LoadSpecResult(sessionId: String, snapshotId: Int, specParameters: SpecParameters)
    extends ExplorationServiceResult

/**
 * Specification parameters that are needed for symbolic path exploration. These numbers may be different from what the
 * user expects by reading the specification, as transitions and invariants are decomposed.
 *
 * @param nInitTransitions
 *   the number of initial symbolic transitions
 * @param nNextTransitions
 *   the number of next symbolic transitions
 * @param nStateInvariants
 *   the number of state invariants
 * @param nActionInvariants
 *   the number of action invariants
 * @param hasView
 *   whether a view predicate is present in the specification
 */
case class SpecParameters(
    nInitTransitions: Int,
    nNextTransitions: Int,
    nStateInvariants: Int,
    nActionInvariants: Int,
    hasView: Boolean)

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
 *   the snapshot ID for recovering the context right after loading the specification.
 * @param newStepNo
 *   the number of the new step
 */
case class NextStepResult(sessionId: String, snapshotId: Int, newStepNo: Int) extends ExplorationServiceResult

/**
 * The result of checking invariants in the current state or transition.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param invariantStatus
 *   the invariant status: "SATISFIED", "VIOLATED", or "UNKNOWN" (also, in case of a timeout)
 * @param trace
 *   a JSON-encoded error trace that shows how the invariant is violated; it is null, if the invariant is not violated
 */
case class CheckInvariantResult(sessionId: String, invariantStatus: InvariantStatus.T, trace: JsonNode)
    extends ExplorationServiceResult

/**
 * The result of querying the current symbolic context.
 * @param sessionId
 *   the ID of the previously loaded specification
 * @param trace
 *   a JSON-encoded trace, if it was requested; otherwise, it is null
 * @param view
 *   a JSON-encoded view, if it was requested; otherwise, it is null
 */
case class QueryResult(sessionId: String, trace: JsonNode, view: JsonNode) extends ExplorationServiceResult
