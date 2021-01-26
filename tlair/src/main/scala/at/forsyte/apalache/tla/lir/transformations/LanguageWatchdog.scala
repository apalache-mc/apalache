package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, LanguagePredError}

/**
  * Given a language predicate, the watchdog checks, whether an expression or a module satisfies the predicate.
  * If not, the watchdog throws UnexpectedLanguageError.
  *
  * @param pred a language predicate
  *
  * @author Igor Konnov
  */
class LanguageWatchdog(pred: LanguagePred) {
  private val predName: String = pred.getClass.getSimpleName

  def check(ex: TlaEx): Unit = {
    pred.isExprOk(ex) match {
      case PredResultOk() =>
        () // do nothing

      case PredResultFail(failedIds) =>
        throw new LanguagePredError(
          s"Some expressions do not fit in the fragment $predName",
          failedIds
        )
    }
  }

  def check(mod: TlaModule): Unit = {
    pred.isModuleOk(mod) match {
      case PredResultOk() =>
        () // do nothing

      case PredResultFail(failedIds) =>
        throw new LanguagePredError(
          s"Some expressions do not fit in the fragment $predName",
          failedIds
        )
    }
  }
}

object LanguageWatchdog {
  def apply(pred: LanguagePred): LanguageWatchdog = {
    new LanguageWatchdog(pred)
  }
}
