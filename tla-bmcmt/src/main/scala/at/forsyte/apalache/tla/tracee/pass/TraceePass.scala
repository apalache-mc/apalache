package at.forsyte.apalache.tla.tracee.pass

import at.forsyte.apalache.tla.imp.passes.PassWithOutputs

/**
 * TODO
 *
 * @author
 *   Jure Kukovec
 */
trait TraceePass extends PassWithOutputs {

  /**
   * For how long the main thread is waiting for the workers to join in case of shutdown.
   */
  val JOIN_TIMEOUT_MS: Long = 5000

  /**
   * The exitcode that is used to stop the system when one thread has failed with an exception.
   */
  val EXITCODE_ON_EXCEPTION = 30

  /**
   * The exitcode that is used to stop the system when the system did not stop gracefully.
   */
  val EXITCODE_ON_SHUTDOWN = 40
}
