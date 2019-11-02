package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, UnexpectedLanguageError}

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
    if (!pred.isExprOk(ex)) {
      throw new UnexpectedLanguageError(s"Predicate $predName does not accept the expression: $ex")
    }
  }

  def check(mod: TlaModule): Unit = {
    if (!pred.isModuleOk(mod)) {
      throw new UnexpectedLanguageError(s"Predicate $predName does not accept the module: ${mod.name}")
    }
  }
}

object LanguageWatchdog {
  def apply(pred: LanguagePred): LanguageWatchdog = {
    new LanguageWatchdog(pred)
  }
}
