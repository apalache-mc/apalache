package at.forsyte.apalache.tla.imp

import at.forsyte.apalache.infra.{ErrorMessage, ExceptionAdapter, NormalErrorMessage}
import at.forsyte.apalache.io.annotations.AnnotationParserError
import com.typesafe.scalalogging.LazyLogging

import javax.inject.{Inject, Singleton}

/**
 * The adapter for all exceptions that can be produced when running the SANY parser and TlaImporter.
 *
 * @author
 *   Igor Konnv
 */
@Singleton
class ParserExceptionAdapter @Inject() () extends ExceptionAdapter with LazyLogging {
  override def toMessage: PartialFunction[Throwable, ErrorMessage] = super.toMessage.orElse {
    case err: SanyException =>
      NormalErrorMessage("Error by TLA+ parser: " + err.getMessage)

    case err: AnnotationParserError =>
      NormalErrorMessage("Syntax error in annotation: " + err.getMessage)
  }
}
