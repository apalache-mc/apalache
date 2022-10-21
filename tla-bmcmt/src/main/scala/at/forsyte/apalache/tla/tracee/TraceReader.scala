package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.io.json.JsonRepresentation
import at.forsyte.apalache.tla.tracee.TraceReader.TraceJson

/**
 * Abstract TraceReader, which can read a trace in some JSON representation, from a source.
 *
 * @author
 *   Jure Kukovec
 */
trait TraceReader[T <: JsonRepresentation] {
  def read(source: SourceOption): TraceJson[T]

  def getTraceLength(traceJson: TraceJson[T]): Int

  def convert(traceJson: TraceJson[T]): Trace
}

object TraceReader {

  /**
   * Wraps a trace json, so the follow-up methods know what shape to expect.
   */
  trait TraceJson[T] {
    val json: T
  }

  sealed case class ITFJson[T](json: T) extends TraceJson[T]
  sealed case class ApalacheJson[T](json: T) extends TraceJson[T]

}
