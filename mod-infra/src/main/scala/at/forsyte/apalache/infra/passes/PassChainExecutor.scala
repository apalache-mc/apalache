package at.forsyte.apalache.infra.passes

import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.MissingTransformationError

/**
 * This class executes the passes starting with the initial one,
 * until the final pass returns None.
 *
 * @param options     the options that can be used by all the passes
 * @param initialPass the first pass to run
 * @author Igor Konnov
 */

class PassChainExecutor @Inject() (val options: WriteablePassOptions, @Named("InitialPass") val initialPass: Pass with TlaModuleMixin)
    extends LazyLogging {

  def run(): Option[Pass] = {
    def exec(seqNo: Int, passToRun: Pass with TlaModuleMixin): Option[Pass] = {
      logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
      val result = passToRun.execute()
      val outcome = if (result) "[OK]" else "[FAIL]"
      logger.debug("PASS #%d: %s %s".format(seqNo, passToRun.name, outcome))
      if (!result) {
        None // return the negative result
      } else {
        val nextPass = passToRun.nextPass
        if (nextPass.hasModule) {
          val module = nextPass.unsafeGetModule

          // Raise error if the pass dependencies aren't satisfied
          if (!nextPass.dependencies.subsetOf(module.properties)) {
            val missing = nextPass.dependencies -- module.properties
            throw new MissingTransformationError(
                s"${nextPass.name} cannot run for a module without the properties: ${missing.mkString(", ")}", module)
          }

          exec(1 + seqNo, nextPass) // call the next pass in line
        } else {
          Some(passToRun) // finished
        }
      }
    }

    exec(0, initialPass)
  }
}
