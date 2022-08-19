package at.forsyte.apalache.infra

import at.forsyte.apalache.infra.passes.Pass
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.ToolModule
import at.forsyte.apalache.infra.passes.WriteablePassOptions
import at.forsyte.apalache.infra.passes.options.OptionGroup
import com.google.inject.Guice
import com.typesafe.scalalogging.LazyLogging

/**
 * This Executor abstracts the dependency injection and execution logic required for executing a PassChainExecutor
 *
 * @param toolModule
 *   The [[infra.passes.ToolModule]] that specifies the sequence of passes
 * @param options
 *   The type of the [[infra.passes.options.OptionGroup OptionsGroup]] interface required to run the specified passes
 *
 * @throws AdaptedException
 *   if any exceptions are caught by the configured [[ExceptionAdapter]]
 *
 * @author
 *   Shon Feder
 */

case class Executor[O <: OptionGroup](val toolModule: ToolModule[O], val options: O) extends LazyLogging {
  private val injector = Guice.createInjector(toolModule)

  /** Exposes mutable access to options configuring the behavior of the [passChainExecutor] */
  // TODO: rm after OptionGroup provider is wired into to replace all access to the PassOptions
  val passOptions = injector.getInstance(classOf[WriteablePassOptions])
  val options = toolModule.options

  private val exceptionAdapter = injector.getInstance(classOf[ExceptionAdapter])

  private val passChainExecutor = {
    val passes = toolModule.passes.zipWithIndex.map { case (p, i) =>
      injector.getInstance(p).withNumber(i)
    }
    new PassChainExecutor(passOptions, passes)
  }

  /** Run the underlying PassChainExecutor, adapting exceptions as needed, and returning a `PassResult` */
  def run(): Pass.PassResult = {
    try {
      passChainExecutor.run()
    } catch {
      case e: Throwable if exceptionAdapter.toMessage.isDefinedAt(e) =>
        // Ensure we can get the full stack trace from the logs
        logger.debug("Adapted exception intercepted: ", e)
        throw new AdaptedException(exceptionAdapter.toMessage(e))
    }
  }

}
