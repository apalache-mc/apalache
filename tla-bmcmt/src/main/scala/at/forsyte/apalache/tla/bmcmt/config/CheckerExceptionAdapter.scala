package at.forsyte.apalache.tla.bmcmt.config

import at.forsyte.apalache.infra.ExceptionAdapter
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.{MalformedTlaError, TlaEx}
import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.pp.NotInKeraError
import javax.inject.{Inject, Singleton}

/**
  * The adapter for all exceptions that can be produced when running the model checker.
  *
  * @author Igor Konnv
  */
@Singleton
class CheckerExceptionAdapter @Inject()(sourceStore: SourceStore,
                                        changeListener: ChangeListener) extends ExceptionAdapter {

  override def toMessage: PartialFunction[Exception, String] = {
    case err: NoRuleException =>
      "%s: no rule to rewrite a TLA+ expression: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: RewriterException =>
      "%s: rewriter error: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: SmtEncodingException =>
      "%s: error when rewriting to SMT: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: TypeException =>
      "%s: type error: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: InvalidTlaExException =>
      "%s: unexpected TLA+ expression: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: InternalCheckerError =>
      "%s: internal error: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: CheckerException =>
      "%s: checker error: %s".format(findLoc(err.causeExpr), err.getMessage)

    case err: NotInKeraError =>
      "%s: expression outside of KerA, report an issue: %s [see docs/kera.md]"
        .format(findLoc(err.causeExpr), err.getMessage)

    case err: MalformedTlaError =>
      "%s: unexpected TLA+ expression: %s".format(findLoc(err.causeExpr), err.getMessage)
  }

  private def findLoc(expr: TlaEx): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(expr) match {
      case Some(loc) => loc.toString
      case None => "<unknown>"
    }
  }
}
