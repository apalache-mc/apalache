package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams
import at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutor

/**
 * A context for running a model checker.
 * @param params model checker parameters such as the step bound, the invariant mode, etc.
 * @param checkerInput checker input that contains the root module, the initial and next transitions, etc.
 * @param trex the transition executor that lets us execute TLA+ transitions symbolically
 * @param listeners model checker listeners that are notified about the progress of the model checker
 * @tparam ExecutorContextT the context type of the transition executor, which can be either
 *                         IncrementalExecutorContext or OfflineExecutorContext
 * @author Igor Konnov
 */
case class ModelCheckerContext[ExecutorContextT](
    params: ModelCheckerParams,
    checkerInput: CheckerInput,
    trex: TransitionExecutor[ExecutorContextT],
    listeners: Seq[ModelCheckerListener] = Nil) {
}
