package at.forsyte.apalache.infra.passes

import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.{MissingTransformationError, TlaModule, TlaModuleProperties}

/**
 * This class executes the passes starting with the initial one,
 * until the final pass returns None.
 *
 * @param options     the options that can be used by all the passes
 * @param initialPass the first pass to run
 * @author Igor Konnov
 */

class PassChainExecutor(val options: WriteablePassOptions, passes: Seq[Pass with TlaModuleMixin]) extends LazyLogging {

  def run(): Option[Pass with TlaModuleMixin] = {
    def exec(seqNo: Int, passToRun: Pass with TlaModuleMixin, module: TlaModule): Option[TlaModule] = {
      logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
      val result = passToRun.execute(module)
      val outcome = if (result.isDefined) "[OK]" else "[FAIL]"
      logger.debug("PASS #%d: %s %s".format(seqNo, passToRun.name, outcome))
      result
    }
    // val result: Option[TlaModule with TlaModuleProperties] = None
    var module = new TlaModule("empty", Seq()) with TlaModuleProperties
    passes.zipWithIndex.foreach { case (pass, index) =>
      // Raise error if the pass dependencies aren't satisfied
      if (!pass.dependencies.subsetOf(module.properties)) {
        val missing = pass.dependencies -- module.properties
        throw new MissingTransformationError(
            s"${pass.name} cannot run for a module without the properties: ${missing.mkString(", ")}", module)
      }

      val transformedModule = exec(index, pass, module)

      transformedModule match {
        case None => return None
        case Some(m) =>
          val newModule = new TlaModule(m.name, m.declarations) with TlaModuleProperties
          newModule.properties = module.properties ++ pass.transformations

          module = newModule
      }
    }
    Some(passes.last)
  }

  // def exec1(seqNo: Int, passToRun: Pass with TlaModuleMixin): Option[Pass with TlaModuleMixin] = {
  //   logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
  //   val result = passToRun.execute()
  //   val outcome = if (result) "[OK]" else "[FAIL]"
  //   logger.debug("PASS #%d: %s %s".format(seqNo, passToRun.name, outcome))
  //   if (!result) {
  //     None // return the negative result
  //   } else {
  //     val nextPass = passToRun.nextPass
  //     if (nextPass.hasModule) {
  //       val module = nextPass.tlaModule.get

  //       // Raise error if the pass dependencies aren't satisfied
  //       if (!nextPass.dependencies.subsetOf(module.properties)) {
  //         val missing = nextPass.dependencies -- module.properties
  //         throw new MissingTransformationError(
  //           s"${nextPass.name} cannot run for a module without the properties: ${missing.mkString(", ")}", module)
  //       }

  //       exec1(1 + seqNo, nextPass) // call the next pass in line
  //     } else {
  //       Some(passToRun) // finished
  //     }
  //   }
  // }

}
