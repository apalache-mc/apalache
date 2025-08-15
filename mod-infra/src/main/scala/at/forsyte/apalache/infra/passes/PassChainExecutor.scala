package at.forsyte.apalache.infra.passes

import at.forsyte.apalache.infra.passes.Pass.PassResult
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.tla.lir.{MissingTransformationError, TlaModule, TlaModuleProperties}
import at.forsyte.apalache.infra.passes.options.OptionGroup
import com.google.inject.{Guice, Injector}
import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.infra.AdaptedException

/**
 * This object executes the passes defined by a [[ToolModule]]. The executor can be executed only once.
 *
 * @throws AdaptedException
 *   if any exceptions are caught by the configured [[ExceptionAdapter]]
 * @throws MissingTransformationError
 *   if passes are executed in an order that causes a passes to be executed without its pass dependencies to be met
 *
 * @author
 *   Igor Konnov, Shon Feder
 */
class PassChainExecutor[O <: OptionGroup](toolModule: ToolModule[O]) extends LazyLogging {
  type PassResultModule = Either[Pass.PassFailure, TlaModule with TlaModuleProperties]
  /**
   * Dependency injector that can be used to extract the constructed objects.
   */
  val injector: Injector = Guice.createInjector(toolModule)
  // has the executor been executed?
  private var isExecuted: Boolean = false

  def run(): PassResult = {
    if (isExecuted) {
      throw new IllegalStateException("PassChainExecutor can only be executed once.")
    }
    isExecuted = true

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

  private def runOnPasses(passes: Seq[Pass]): PassResultModule = passes.foldLeft(initialModule)(runPassOnModule)

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

object PassChainExecutor {
  def apply(toolModule: ToolModule[_ <: OptionGroup]): PassChainExecutor[_ <: OptionGroup] = {
    new PassChainExecutor(toolModule)
  }
}