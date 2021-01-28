package at.forsyte.apalache.tla.bmcmt.trex

/**
  * A snapshot of TransitionExecutor.
  *
  * @param controlState executor's control state
  * @param execution symbolic execution that has been constructed so far
  * @param preparedTransitions a map of symbolic transitions
  * @param contextSnapshot a snapshot of the executor's context
  * @tparam ExecutorContextSnapshotT the type of the context snapshot
  */
class ExecutionSnapshot[ExecutorContextSnapshotT](
    val controlState: ExecutorControlState,
    val execution: EncodedExecution,
    val preparedTransitions: Map[Int, EncodedTransition],
    val contextSnapshot: ExecutorContextSnapshotT
)
