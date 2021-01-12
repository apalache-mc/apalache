package at.forsyte.apalache.tla.bmcmt.trex

class ExecutorSnapshot[ExecCtxT](val controlState: ExecutorControlState,
                                 val execution: ReducedExecution,
                                 val preparedTransitions: Map[Int, ReducedTransition],
                                 val ctxSnapshot: ExecCtxT)
