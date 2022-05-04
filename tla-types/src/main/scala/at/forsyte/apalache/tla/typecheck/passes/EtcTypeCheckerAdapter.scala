package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.{ErrorMessage, ExceptionAdapter, FailureMessage, NormalErrorMessage}
import at.forsyte.apalache.io.annotations.AnnotationParserError
import at.forsyte.apalache.tla.imp.SanyException
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.{OutdatedAnnotationsError, TypingException, UID}
import at.forsyte.apalache.tla.typecheck.TypingInputException
import com.google.inject.{Inject, Singleton}
import com.typesafe.scalalogging.LazyLogging

/**
 * The adapter for the exceptions that are produced by the parser and type checker.
 *
 * @author
 *   Igor Konnov
 */
@Singleton
class EtcTypeCheckerAdapter @Inject() (sourceStore: SourceStore, changeListener: ChangeListener)
    extends ExceptionAdapter with LazyLogging {
  override def toMessage: PartialFunction[Throwable, ErrorMessage] = {
    case err: OutOfMemoryError =>
      logger.error(s"Ran out of heap memory (max JVM memory: ${Runtime.getRuntime.maxMemory})")
      logger.error(s"To increase available heap memory, see the manual:")
      logger.error("  [https://apalache.informal.systems/docs/apalache/running.html#supplying-jvm-arguments]")
      NormalErrorMessage(s"Ran out of heap memory: ${err.getMessage}")

    case err: SanyException =>
      NormalErrorMessage("Error by TLA+ parser: " + err.getMessage)

    case err: AnnotationParserError =>
      NormalErrorMessage("Syntax error in annotation: " + err.getMessage)

    case err: TypingInputException =>
      NormalErrorMessage("Typing input error: " + err.getMessage)

    case err: OutdatedAnnotationsError =>
      val msg = "%s: rewriter error: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      NormalErrorMessage(msg)

    case err: TypingException =>
      FailureMessage("Type checker error: " + err.getMessage)
  }

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "<unknown>"
    }
  }
}
