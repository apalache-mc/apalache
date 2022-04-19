package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}

/**
 * Observe [[SeqModelChecker]]. State changes in model checker state are reported via callbacks.
 */
trait ModelCheckerListener {

  /**
   * Call when the model checker encounters a counterexample.
   *
   * @param rootModule
   *   The checked TLA+ module.
   * @param trace
   *   The counterexample trace.
   * @param invViolated
   *   The invariant violation to record in the counterexample. Pass
   *   - for invariant violations: the negated invariant,
   *   - for deadlocks: `ValEx(TlaBool(true))`,
   *   - for trace invariants: the applied, negated trace invariant (see [[SeqModelChecker.applyTraceInv]]).
   * @param errorIndex
   *   Number of found error (likely [[SearchState.nFoundErrors]]).
   */
  def onCounterexample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      errorIndex: Int): Unit
}
