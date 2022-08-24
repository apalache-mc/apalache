package at.forsyte.apalache.infra

import at.forsyte.apalache.infra.passes.{Pass, PassChainExecutor, ToolModule, WriteablePassOptions}
import com.google.inject.Guice
import com.typesafe.scalalogging.LazyLogging

/**
 * This Executor abstracts the dependency injection and execution logic required for executing a PassChainExecutor
 *
 * @param toolModule
 *   The [[infra.passes.ToolModule]] that specifies the sequence of passes
 * @throws AdaptedException
 *   if any exceptions are caught by the configured [[ExceptionAdapter]]
 * @author
 *   Shon Feder
 */
case class Executor(val toolModule: ToolModule) extends LazyLogging {
  private val injector = Guice.createInjector(toolModule)

  /** Exposes mutable access to options configuring the behavior of the [passChainExecutor] */
  val passOptions = injector.getInstance(classOf[WriteablePassOptions])

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
