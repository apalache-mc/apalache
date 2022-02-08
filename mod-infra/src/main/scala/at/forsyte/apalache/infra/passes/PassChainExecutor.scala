package at.forsyte.apalache.infra.passes

import com.google.inject.Inject
import com.google.inject.name.Named
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.{MissingTransformationError, TlaModule, TlaModuleProperties, ModuleProperty}

/**
 * This class executes the passes starting with the initial one,
 * until the final pass returns None.
 *
 * @param options     the options that can be used by all the passes
 * @param initialPass the first pass to run
 * @author Igor Konnov
 */

class PassChainExecutor(val options: WriteablePassOptions, passes: Seq[Pass]) extends LazyLogging {

  def run(): Option[TlaModule] = {
    def exec(seqNo: Int, passToRun: Pass, module: TlaModule): Option[TlaModule] = {
      logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
      val result = passToRun.execute(module)
      val outcome = if (result.isDefined) "[OK]" else "[FAIL]"
      logger.debug("PASS #%d: %s %s".format(seqNo, passToRun.name, outcome))
      result
    }

    def checkDependencies(module: TlaModule with TlaModuleProperties, pass: Pass): Unit = {
      if (!pass.dependencies.subsetOf(module.properties)) {
        val missing = pass.dependencies -- module.properties
        throw new MissingTransformationError(
            s"${pass.name} cannot run for a module without the properties: ${missing.mkString(", ")}", module)
      }
    }

    passes.zipWithIndex
      .foldLeft(Option[TlaModule with TlaModuleProperties](new TlaModule("empty", Seq()) with TlaModuleProperties)) {
        case (moduleOpt, (pass, index)) =>
          // Raise error if the pass dependencies aren't satisfied
          moduleOpt.map { m => checkDependencies(m, pass) }

          for {
            module <- moduleOpt
            transformedModule <- exec(index, pass, module)
          } yield {
            val newModule = new TlaModule(transformedModule.name, transformedModule.declarations)
              with TlaModuleProperties
            newModule.properties = module.properties ++ pass.transformations
            newModule
          }
      }
  }
}
