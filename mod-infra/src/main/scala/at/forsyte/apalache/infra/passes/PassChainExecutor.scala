package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import at.forsyte.apalache.infra.passes.Pass.PassResult
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.{MissingTransformationError, TlaModule, TlaModuleProperties}

/**
 * This class executes the passes starting with the initial one, until the final pass returns None.
 *
 * @param options
 *   the options that can be used by all the passes
 * @param initialPass
 *   the first pass to run
 * @author
 *   Igor Konnov
 */

class PassChainExecutor(val options: WriteablePassOptions, passes: Seq[Pass]) extends LazyLogging {
  def run(): PassResult = {
    def exec(seqNo: Int, passToRun: Pass, module: TlaModule): PassResult = {
      logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
      val result = passToRun.execute(module)
      val outcome = result.fold(_ => "[FAIL]", _ => "[OK]")
      // TODO: As part of #858, PassWithOutputs.writeOut should be called here.
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

    val emptyModuleWithProperties: TlaModule with TlaModuleProperties = new TlaModule("empty", Seq())
      with TlaModuleProperties
    val startValue: Either[TExitCode, TlaModule with TlaModuleProperties] = Right(emptyModuleWithProperties)
    passes.zipWithIndex.foldLeft(startValue) { case (moduleOpt, (pass, index)) =>
      // Raise error if the pass dependencies aren't satisfied
      moduleOpt.map { m => checkDependencies(m, pass) }

      for {
        module <- moduleOpt
        transformedModule <- exec(index, pass, module)
      } yield {
        val newModule = new TlaModule(transformedModule.name, transformedModule.declarations) with TlaModuleProperties
        newModule.properties = module.properties ++ pass.transformations
        newModule
      }
    }
  }
}
