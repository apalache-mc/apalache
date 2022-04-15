package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.lir.CounterexampleWriter
import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution
import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}
import com.typesafe.scalalogging.LazyLogging

/**
 * Observer to [[SeqModelChecker]] that dumps counterexamples to files.
 */
object DumpCounterexamplesModelCheckerListener extends ModelCheckerListener with LazyLogging {

  /**
   * Call when [[SeqModelChecker]] encounters a counterexample. Dumps counterexample to files.
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
    val states = trace.path.map(p => (p._2.toString, p._1))

    def dump(suffix: String): List[String] = {
      CounterexampleWriter.writeAllFormats(suffix, rootModule, invViolated, states)
    }

    // for a human user, write the latest counterexample into counterexample.{tla,json}
    dump("")

    // for automation scripts, produce counterexample${nFoundErrors}.{tla,json}
    val filenames = dump(errorIndex.toString)

    logger.error(s"Check an example state in: ${filenames.mkString(", ")}")
  }
}
