package at.forsyte.apalache.tla.tracee

import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.types._

/**
 * @author
 *   Jure Kukovec
 */
class TraceReader {

  // TODO
  def get(): Trace = (1 to (5)).map { i =>
    Map("x" -> tla.int(i))
  }

}
