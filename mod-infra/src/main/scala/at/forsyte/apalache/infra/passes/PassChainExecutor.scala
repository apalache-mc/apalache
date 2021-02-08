package at.forsyte.apalache.infra.passes

import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging

/**
 * This class executes the passes starting with the initial one,
 * until the final pass returns None.
 *
 * @param options     the options that can be used by all the passes
 * @param initialPass the first pass to run
 * @author Igor Konnov
 */

class PassChainExecutor @Inject() (val options: WriteablePassOptions, @Named("InitialPass") val initialPass: Pass)
    extends LazyLogging {

  def run(): Option[Pass] = {
    def exec(seqNo: Int, passToRun: Pass): Option[Pass] = {
      logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
      val result = passToRun.execute()
      val outcome = if (result) "[OK]" else "[FAIL]"
      logger.debug("PASS #%d: %s %s".format(seqNo, passToRun.name, outcome))
      if (!result) {
        None // return the negative result
      } else {
        val nextPass = passToRun.next()
        if (nextPass.isDefined) {
          exec(1 + seqNo, nextPass.get) // call the next pass in line
        } else {
          Some(passToRun) // finished
        }
      }
    }

    exec(0, initialPass)
  }
}
