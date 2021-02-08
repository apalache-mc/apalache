package at.forsyte.apalache.infra

/**
 * An abstract error message.
 */
sealed abstract class ErrorMessage

/**
 * A normal error that does not require a stack trace.
 * @param msg the message text
 */
case class NormalErrorMessage(msg: String) extends ErrorMessage

/**
 * A failure message that should be printed along with a stack trace.
 * @param msg the message text
 */
case class FailureMessage(msg: String) extends ErrorMessage

/**
 * ExceptionAdapter allows us to convert an exception into a message string.
 * The purpose of the adapter is to push the conversion in the DI container, where all required data is available,
 * e.g., source data.
 *
 * @author Igor Konnov
 */
trait ExceptionAdapter {
  def toMessage: PartialFunction[Exception, ErrorMessage]
}
