package at.forsyte.apalache.infra

import com.typesafe.scalalogging.LazyLogging

/**
 * An abstract error message.
 */
sealed abstract class ErrorMessage {

  /** The concrete content of a message */
  val msg: String
}

/**
 * A normal error that does not require a stack trace.
 * @param msg
 *   the message text
 */
case class NormalErrorMessage(val msg: String) extends ErrorMessage

/**
 * A failure message that should be printed along with a stack trace.
 * @param msg
 *   the message text
 */
case class FailureMessage(val msg: String) extends ErrorMessage

/**
 * ExceptionAdapter allows us to convert an exception into a message string. The purpose of the adapter is to push the
 * conversion in the DI container, where all required data is available, e.g., source data.
 *
 * @author
 *   Igor Konnov
 */
trait ExceptionAdapter extends LazyLogging {
  def toMessage: PartialFunction[Throwable, ErrorMessage] = { case err: OutOfMemoryError =>
    logger.error(s"Ran out of heap memory (max JVM memory: ${Runtime.getRuntime.maxMemory})")
    logger.error(s"To increase available heap memory, see the manual:")
    logger.error("  [https://apalache-mc.org/docs/apalache/running.html#supplying-jvm-arguments]")
    NormalErrorMessage(s"Ran out of heap memory: ${err.getMessage}")
  }
}
