package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.{ErrorMessage, ExceptionAdapter, FailureMessage, NormalErrorMessage}
import at.forsyte.apalache.tla.imp.SanyException
import at.forsyte.apalache.tla.typecheck.{TypingException, TypingInputException}
import com.google.inject.{Inject, Singleton}

/**
 * The adapter for the exceptions that are produced by the parser and type checker.
 *
 * @author Igor Konnov
 */
@Singleton
class EtcTypeCheckerAdapter @Inject() () extends ExceptionAdapter {
  override def toMessage: PartialFunction[Exception, ErrorMessage] = {
    case err: SanyException =>
      NormalErrorMessage("Error by TLA+ parser: " + err.getMessage)

    case err: TypingInputException =>
      NormalErrorMessage("Typing input error: " + err.getMessage)

    case err: TypingException =>
      FailureMessage("Type checker error: " + err.getMessage)
  }
}
