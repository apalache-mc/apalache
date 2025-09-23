package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule}

import scala.collection.immutable.SortedSet

/**
 * Representation of a trace found while model checking. The trace may represent an example or a counterexample.
 *
 * @param module
 *   The checked TLA+ module.
 * @param states
 *   The sequence of states in the trace.
 * @param labels
 *   The sequence of labels for each state. Normally, these are the transition labels.
 * @param data
 *   Additional data that can be attached to the counterexample, e.g., the negated invariant.
 *   The most common use case is to attach the negated invariant for invariant violations:
 *    - for invariant violations: the negated invariant,
 *    - for deadlocks: `ValEx(TlaBool(true))`,
 *    - for trace invariants: the applied, negated trace invariant
 *
 * @author
 *   Shon Feder, Igor Konnov
 */
case class Trace[T](
                     module: TlaModule,
                     states: IndexedSeq[Trace.State],
                     labels: IndexedSeq[SortedSet[String]],
                     data: T)

object Trace {
  import upickle.default.{writer, Writer}

  type State = Map[String, TlaEx]

  // Defines an implicit view for converting to UJSON
  implicit val ujsonView: Trace[TlaEx] => ujson.Value = { case Trace(module, states, _, _) =>
    ItfCounterexampleWriter.mkJson(module, states)
  }

  // Defines an implicit converter for writing with upickle
  implicit val upickleWriter: Writer[Trace[TlaEx]] =
    writer[ujson.Value].comap(ujsonView)
}
