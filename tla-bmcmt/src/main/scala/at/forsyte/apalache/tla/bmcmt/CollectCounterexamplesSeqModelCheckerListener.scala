package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable.ListBuffer

/**
 * Observer to [[SeqModelChecker]] that collects all counterexamples in [[counterExamples]].
 */
class CollectCounterexamplesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  /**
   * Call when the model checker encounters a counterexample. Dumps counterexample to files.
   *
   * The counterexample trace is written to the following files:
   *   - `counterexample${errorIndex}.{tla,json,.itf.json}` contains the current counterexample
   *   - `counterexample.{tla,json,.itf.json}` contains the latest counterexample
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
  override def onCounterexample(
      rootModule: TlaModule,
      trace: DecodedExecution,
      invViolated: TlaEx,
      errorIndex: Int): Unit = {
    _counterExamples += trace
  }

  private val _counterExamples = ListBuffer.empty[DecodedExecution]
  def counterExamples: Seq[DecodedExecution] = _counterExamples
}
