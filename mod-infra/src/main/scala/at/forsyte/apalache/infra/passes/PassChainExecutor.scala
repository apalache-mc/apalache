package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.{MissingTransformationError, TlaModule, TlaModuleProperties}
import at.forsyte.apalache.infra.passes.options.OptionGroup
import com.google.inject.Guice
import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.AdaptedException

/**
 * This object executes the passes defined by a [[ToolModule]]
 *
 * @throws AdaptedException
 *   if any exceptions are caught by the configured [[ExceptionAdapter]]
 * @throws tla.lir.MissingTransformationError
 *   if passes are executed in an order that causes a passes to be executed without its pass dependencies to be met
 *
 * @author
 *   Igor Konnov, Shon Feder
 */
object PassChainExecutor extends LazyLogging {

  type PassResultModule = Either[Pass.PassFailure, TlaModule with TlaModuleProperties]

  def run[O <: OptionGroup](toolModule: ToolModule[O]): PassResult = {

    val injector = Guice.createInjector(toolModule)
    val exceptionAdapter = injector.getInstance(classOf[ExceptionAdapter])

    val passes = toolModule.passes.zipWithIndex.map { case (p, i) => injector.getInstance(p).withNumber(i) }

    try {
      runOnPasses(passes)
    } catch {
      case e: Throwable if exceptionAdapter.toMessage.isDefinedAt(e) =>
        // Ensure we can get the full stack trace from the logs
        logger.debug("Adapted exception intercepted: ", e)
        throw new AdaptedException(exceptionAdapter.toMessage(e))
    }
  }

  // Allow use elsewhere in the package for testing
  private[passes] def runOnPasses(passes: Seq[Pass]): PassResultModule = passes.foldLeft(initialModule)(runPassOnModule)

  // The module used to initiate a pass execution
  private val initialModule: PassResultModule = Right(new TlaModule("empty", Seq()) with TlaModuleProperties)

  private val runPassOnModule: (PassResultModule, Pass) => PassResultModule = (resultModule, pass) => {
    for {
      module <- resultModule
      _ = checkDependencies(module, pass) // Raise error if the pass dependencies aren't satisfied
      transformedModule <- exec(pass.passNumber, pass, module)
    } yield {
      val newModule = new TlaModule(transformedModule.name, transformedModule.declarations) with TlaModuleProperties
      newModule.properties = module.properties ++ pass.transformations
      newModule
    }
  }

  // Execute a single pass on a module
  private def exec(seqNo: Int, passToRun: Pass, module: TlaModule): PassResult = {
    logger.info("PASS #%d: %s".format(seqNo, passToRun.name))
    val result = passToRun.execute(module)
    val outcome = result.fold(_ => "[FAIL]", _ => "[OK]")
    // TODO: As part of #858, PassWithOutputs.writeOut should be called here.
    logger.debug("PASS #%d: %s %s".format(seqNo, passToRun.name, outcome))
    result
  }

  // Check that all the required pass dependencies of a module have been met
  private def checkDependencies(module: TlaModule with TlaModuleProperties, pass: Pass): Unit = {
    if (!pass.dependencies.subsetOf(module.properties)) {
      val missing = pass.dependencies -- module.properties
      throw new MissingTransformationError(
          s"${pass.name} cannot run for a module without the properties: ${missing.mkString(", ")}", module)
    }
  }
}
