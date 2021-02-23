package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{TlaEx, TlaModule, UID}

/**
 * The type of the output that the predicate returns
 */
trait PredResult {

  /**
   * Combine the result with another one, similar to Boolean "and".
   * @param other the result to combine with
   */
  def and(other: PredResult): PredResult = {
    (this, other) match {
      case (PredResultOk(), PredResultOk())               => PredResultOk()
      case (PredResultOk(), f @ PredResultFail(_))        => f
      case (f @ PredResultFail(_), PredResultOk())        => f
      case (PredResultFail(errs1), PredResultFail(errs2)) => PredResultFail(errs1 ++ errs2)
    }
  }
}

/**
 * This type of result is returned when the predicate does not fail.
 */
sealed case class PredResultOk() extends PredResult

/**
 * This type of result is returned when the predicate fails with an error.
 * @param failedIds the identifiers of the expressions that raised the error along with the explanations
 */
sealed case class PredResultFail(failedIds: Seq[(UID, String)]) extends PredResult

/**
 * <p>A class that implements LanguagePred checks, whether a TLA+ expression, or a whole module,
 * fits into a fragment of TLA+. For instance, FlatLanguagePred expects that all user operators have been inlined.</p>
 *
 * <p>The most reasonable usage for a language predicate is to use in conjunction with LanguageWatchdog,
 * which fails immediately, once an expression is outside of the expected fragment.
 * This feature addresses issue #68.</p>
 *
 * @author Igor Konnov
 */
trait LanguagePred {

  def isExprOk(ex: TlaEx): PredResult

  def isModuleOk(mod: TlaModule): PredResult
}
