package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.TlaModule

/**
 * Observe [[SeqModelChecker]]. State changes in model checker state are reported via callbacks.
 */
trait ModelCheckerListener {

  /**
   * Call when the model checker encounters a counterexample.
   *
   * @param counterexample
   *   The counterexample to record
   * @param errorIndex
   *   Number of found error (likely [[search.SearchState.nFoundErrors]]).
   */
  // For more on possible trace invariant violations, see the private method `SeqModelChecker.applyTraceInv`
  def onCounterexample(
      counterexample: Counterexample,
      errorIndex: Int): Unit

  /**
   * Call when the model checker outputs an example of an execution (for the user to observe)
   *
   * @param rootModule
   *   The checked TLA+ module.
   * @param trace
   *   The example trace
   * @param exampleIndex
   *   The example number (likely [[search.SearchState.nRunsLeft]])
   */
  def onExample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      exampleIndex: Int): Unit
}
