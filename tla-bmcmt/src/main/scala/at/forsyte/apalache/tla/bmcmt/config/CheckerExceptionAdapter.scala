package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.{ErrorMessage, ExceptionAdapter, FailureMessage, NormalErrorMessage}
import at.forsyte.apalache.tla.assignments.{AssignmentException, CoverData}
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.imp.SanyException
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.lir.{
  LanguagePredError, MalformedTlaError, OperEx, OutdatedAnnotationsError, TypingException, UID
}
import at.forsyte.apalache.tla.pp.{
  ConfigurationError, IrrecoverablePreprocessingError, NotInKeraError, OverridingError, TlaInputError
}
import at.forsyte.apalache.tla.typecheck.TypingInputException
import com.typesafe.scalalogging.LazyLogging

import javax.inject.{Inject, Singleton}

/**
 * The adapter for all exceptions that can be produced when running the model checker.
 *
 * @author Igor Konnv
 */
@Singleton
class CheckerExceptionAdapter @Inject() (sourceStore: SourceStore, changeListener: ChangeListener)
    extends ExceptionAdapter with LazyLogging {
  private lazy val ISSUES_LINK: String = "[https://github.com/informalsystems/apalache/issues]"

  override def toMessage: PartialFunction[Exception, ErrorMessage] = {
    // normal errors
    case err: SanyException =>
      NormalErrorMessage("Error by TLA+ parser: " + err.getMessage)

    case err: ConfigurationError =>
      NormalErrorMessage("Configuration error (see the manual): " + err.getMessage)

    case err: OverridingError =>
      NormalErrorMessage("Configuration error (see the manual): " + err.getMessage)

    case err: TlaInputError =>
      NormalErrorMessage("Input error (see the manual): " + err.getMessage)

    case err: AssignmentException =>
      logger.info("To understand the error, read the manual:")
      logger.info("  [https://apalache.informal.systems/docs/apalache/principles.html#assignments]")
      NormalErrorMessage("Assignment error: " + err.getMessage)

    case err: OutdatedAnnotationsError =>
      val msg = "%s: rewriter error: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      NormalErrorMessage(msg)

    case err: LanguagePredError =>
      // a language predicate failed
      err.failedIds.foreach { idAndMsg =>
        logger.error("%s: unexpected expression: %s".format(findLoc(idAndMsg._1), idAndMsg._2))
      }
      NormalErrorMessage("Unexpected expressions in the specification (see the error messages)")

    case err: NotInKeraError =>
      NormalErrorMessage("%s: Input error (see the manual): %s".format(findLoc(err.causeExpr.ID), err.getMessage))

    case err: TypingInputException =>
      NormalErrorMessage("Typing input error: " + err.getMessage)

    case err: TypingException =>
      FailureMessage("Type checker error: " + err.getMessage)

    // tool failures
    case err: IrrecoverablePreprocessingError =>
      val msg = s"Irrecoverable preprocessing error: ${err.getMessage}. Report an issue at $ISSUES_LINK"
      FailureMessage(msg)

    case err: NoRuleException =>
      val msg =
        "%s: no rule to rewrite a TLA+ expression: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: RewriterException =>
      val msg = "%s: rewriter error: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: SmtEncodingException =>
      val msg = "%s: error when rewriting to SMT: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: TypeException =>
      FailureMessage("%s: type error: %s".format(findLoc(err.causeExpr.ID), err.getMessage))

    case err: InvalidTlaExException =>
      val msg = "%s: unexpected TLA+ expression: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: InternalCheckerError =>
      val msg = "%s: internal error: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: CheckerException =>
      val msg = "%s: checker error: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: MalformedTlaError =>
      val msg = "%s: unexpected TLA+ expression: %s".format(findLoc(err.causeExpr.ID), err.getMessage)
      FailureMessage(msg)

    case err: CoverData.CoverException =>
      val msg =
        "Unable to find assignments for all state variables: \n%s\n [see https://apalache.informal.systems/docs/apalache/principles.html#assignments]"
          .format(err.getMessage)
      NormalErrorMessage(msg)
  }

  private def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "<unknown>"
    }
  }
}
