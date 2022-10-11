package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.tla.types.tla

/**
 * @author
 *   Jure Kukovec
 */
class TraceReader {

  // TODO: Until #2201 is implemented, we don't actually read the trace, we just fix one.
  def get(): Trace = (1 to (5)).map { i =>
    Map("x" -> tla.int(i))
  }

}
