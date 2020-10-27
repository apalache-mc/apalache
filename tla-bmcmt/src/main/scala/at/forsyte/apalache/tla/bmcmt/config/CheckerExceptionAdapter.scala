package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.{ErrorMessage, ExceptionAdapter, FailureMessage, NormalErrorMessage}
import at.forsyte.apalache.tla.assignments.{AssignmentException, CoverData}
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.TypeInferenceError
import at.forsyte.apalache.tla.imp.SanyException
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{MalformedTlaError, OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.pp.{ConfigurationError, IrrecoverablePreprocessingError, NotInKeraError, TLCConfigurationError, TlaInputError}
import com.typesafe.scalalogging.LazyLogging
import javax.inject.{Inject, Singleton}

/**
  * The adapter for all exceptions that can be produced when running the model checker.
  *
  * @author Igor Konnv
  */
@Singleton
class CheckerExceptionAdapter @Inject()(sourceStore: SourceStore,
                                        changeListener: ChangeListener) extends ExceptionAdapter with LazyLogging {
  private lazy val ISSUES_LINK: String = "[https://github.com/informalsystems/apalache/issues]"

  override def toMessage: PartialFunction[Exception, ErrorMessage] = {
    // normal errors
    case err: SanyException =>
      NormalErrorMessage("Error by TLA+ parser: " + err.getMessage)

    case err: ConfigurationError =>
      NormalErrorMessage("Configuration error (see the manual): " + err.getMessage)

    case err: TlaInputError =>
      NormalErrorMessage("Input error (see the manual): " + err.getMessage)

    case err: AssignmentException =>
      logger.info("To understand the error, read the manual:")
      logger.info("  [https://github.com/informalsystems/apalache/blob/unstable/docs/manual.md#assignments]")
      NormalErrorMessage("Assignment error: " + err.getMessage)

    case err: TypeInferenceException =>
      val msg = "%s\n%s".format(err.getMessage, err.errors.map(ofTypeInferenceError).mkString("\n"))
      NormalErrorMessage(msg)

    case err: NotInKeraError =>
      NormalErrorMessage("Input error (see the manual): " + err.getMessage)

    // tool failures
    case err: IrrecoverablePreprocessingError =>
      val msg = s"Irrecoverable preprocessing error: ${err.getMessage}. Report an issue at $ISSUES_LINK"
      FailureMessage(msg)

    case err: NoRuleException =>
      val msg =
        "%s: no rule to rewrite a TLA+ expression: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: RewriterException =>
      val msg = "%s: rewriter error: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: SmtEncodingException =>
      val msg = "%s: error when rewriting to SMT: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: TypeException =>
      FailureMessage("%s: type error: %s".format(findLoc(err.causeExpr), err.getMessage))

    case err: InvalidTlaExException =>
      val msg = "%s: unexpected TLA+ expression: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: InternalCheckerError =>
      val msg = "%s: internal error: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: CheckerException =>
      val msg = "%s: checker error: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: NotInKeraError =>
      val msg = "%s: expression outside of the supported fragment KerA, report an issue: %s [see docs/kera.md]".
        format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: MalformedTlaError =>
      val msg = "%s: unexpected TLA+ expression: %s".format(findLoc(err.causeExpr), err.getMessage)
      FailureMessage(msg)

    case err: CoverData.CoverException =>
      val msg = "Unable to find assignments for all state variables: \n%s\n [see docs/manual.md 7.1]".format(err.getMessage)
      NormalErrorMessage(msg)
  }

  private def findLoc(expr: TlaEx): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(expr) match {
      case Some(loc) => loc.toString
      case None => "<unknown>"
    }
  }

  def ofTypeInferenceError(e: TypeInferenceError): String = {
    val locInfo = findLoc(e.origin)
    val exStr = e.origin match {
      case OperEx(op, _*) => op.name
      case ex@_ => ex.toString()
    }
    "%s, %s, type error: %s".format(locInfo, exStr, e.explanation)
  }
}
