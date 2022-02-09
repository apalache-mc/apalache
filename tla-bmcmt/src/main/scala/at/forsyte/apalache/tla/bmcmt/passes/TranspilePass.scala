package at.forsyte.apalache.tla.bmcmt.passes

import at.forsyte.apalache.infra.passes.Pass

trait TranspilePass extends Pass {

  /**
   * The exitcode that is used to stop the system when one thread has failed with an exception.
   */
  val EXITCODE_ON_EXCEPTION = 30

  /**
   * The exitcode that is used to stop the system when the system did not stop gracefully.
   */
  val EXITCODE_ON_SHUTDOWN = 40
}
