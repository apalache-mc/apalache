package at.forsyte.apalache.tla.tracee.pass

import at.forsyte.apalache.tla.passes.imp.PassWithOutputs

/**
 * TODO
 *
 * @author
 *   Jure Kukovec
 */
trait TraceePass extends PassWithOutputs {

  /**
   * The exitcode that is used to stop the system when one thread has failed with an exception.
   */
  val EXITCODE_ON_EXCEPTION = 30
}
