package at.forsyte.apalache.infra

import at.forsyte.apalache.infra.passes.Pass
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.ToolModule
import at.forsyte.apalache.infra.passes.options.OptionGroup
import com.google.inject.Guice
import com.typesafe.scalalogging.LazyLogging

/**
 * `Executor` class abstracts the dependency injection and execution logic required for executing a
 * [[infra.passes.PassChainExecutor PassChainExecutor]]
 *
 * The `Exectuor` is parameterized by a [[infra.passes.options.OptionGroup]] subclass. Typically, the actual type
 * provided is one of the `OptionGroup` interfaces `Has*`. This is used to statically declare the set of configuration
 * parameters upon which the pass chain execution depends.
 *
 * @param toolModule
 *   The [[infra.passes.ToolModule]] that specifies the sequence of passes
 *
 * @throws AdaptedException
 *   if any exceptions are caught by the configured [[ExceptionAdapter]]
 *
 * @author
 *   Shon Feder
 */

case class Executor[O <: OptionGroup](val toolModule: ToolModule[O]) extends LazyLogging {
  private val injector = Guice.createInjector(toolModule)

  private val exceptionAdapter = injector.getInstance(classOf[ExceptionAdapter])

  private val passChainExecutor = {
    val passes = toolModule.passes.zipWithIndex.map { case (p, i) =>
      injector.getInstance(p).withNumber(i)
    }
    new PassChainExecutor(passes)
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
