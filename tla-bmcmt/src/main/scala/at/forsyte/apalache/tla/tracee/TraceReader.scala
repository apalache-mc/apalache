package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.io.json.JsonRepresentation

/**
 * Abstract TraceReader, which can read a trace in some JSON representation, from a source.
 *
 * @author
 *   Jure Kukovec
 */
trait TraceReader[T <: JsonRepresentation] {
  def read(source: SourceOption): T

  def convert(json: T): Trace
}
