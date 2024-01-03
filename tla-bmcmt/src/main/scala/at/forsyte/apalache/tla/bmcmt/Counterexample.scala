package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.io.lir.ItfCounterexampleWriter
import at.forsyte.apalache.tla.bmcmt.trex.DecodedExecution

/**
 * Representation of a counterexample found while model checking
 *
 * @param rootModule
 *   The checked TLA+ module.
 * @param states
 *   The states leading up to the invariant violation.
 * @param invViolated
 *   The invariant violation to record in the counterexample. Pass
 *   - for invariant violations: the negated invariant,
 *   - for deadlocks: `ValEx(TlaBool(true))`,
 *   - for trace invariants: the applied, negated trace invariant
 *
 * @author
 *   Shon Feder
 */
case class Counterexample(module: TlaModule, states: Counterexample.States, invViolated: TlaEx)

object Counterexample {
  type States = List[(String, Map[String, TlaEx])]

  import upickle.default.{writer, Writer}

  // Defines an implicit view for converting to UJSON
  implicit val ujsonView: Counterexample => ujson.Value = { case Counterexample(module, states, _) =>
    ItfCounterexampleWriter.mkJson(module, states)
  }

  // Defines an implicit converter for writing with upickle
  implicit val upickleWriter: Writer[Counterexample] =
    writer[ujson.Value].comap(ujsonView)

  /** Produce a `Counterexample` from a `trace` (rather than from `states`) */
  def apply(module: TlaModule, trace: DecodedExecution, invViolated: TlaEx): Counterexample = {
    // TODO(shonfeder): This conversion seems kind of senseless: we just swap the tuple and convert the transition index to
    // a string. Lots depends on this particular format, but it seems like a pretty pointless intermediary structure?
    val states = trace.path.map(p => (p._2.toString, p._1))
    Counterexample(module, states, invViolated)
  }
}
