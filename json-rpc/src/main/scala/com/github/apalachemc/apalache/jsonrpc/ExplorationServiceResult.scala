package com.github.apalachemc.apalache.jsonrpc

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
 * @param nTraceInvariants
 *   the number of trace invariants
 * @param hasView
 *   whether a view predicate is present in the specification
 */
case class SpecParameters(
                           nInitTransitions: Int,
                           nNextTransitions: Int,
                           nStateInvariants: Int,
                           nActionInvariants: Int,
                           nTraceInvariants: Int,
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