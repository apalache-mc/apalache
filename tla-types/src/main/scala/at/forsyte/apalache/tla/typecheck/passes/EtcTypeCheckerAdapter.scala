package at.forsyte.apalache.tla.typecheck.passes

import at.forsyte.apalache.infra.{ErrorMessage, ExceptionAdapter, FailureMessage, NormalErrorMessage}
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
 * @author Igor Konnov
 */
@Singleton
class EtcTypeCheckerAdapter @Inject() (sourceStore: SourceStore, changeListener: ChangeListener)
    extends ExceptionAdapter with LazyLogging {
  override def toMessage: PartialFunction[Exception, ErrorMessage] = {
    case err: SanyException =>
      NormalErrorMessage("Error by TLA+ parser: " + err.getMessage)

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
