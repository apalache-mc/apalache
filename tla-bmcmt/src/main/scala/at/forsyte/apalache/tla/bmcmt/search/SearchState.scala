package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.tla.bmcmt.Checker

/**
 * The search state machine that is implemented by SeqModelChecker.
 * This machine is simple when the model checker fails on the first error.
 * It becomes complex when multiple errors are allowed.
 *
 * @param params model checker parameters
 * @author Igor Konnov
 */
class SearchState(params: ModelCheckerParams) {

  import Checker._

  private var _result: CheckerResult = NoError()
  private var _nFoundErrors: Int = 0

  /**
   * Get the number of errors that were found so far (excluding deadlocks and runtime errors).
   *
   * @return number of found errors
   */
  def nFoundErrors: Int = _nFoundErrors

  /**
   * Get the cumulative result of the machine.
   *
   * @return NoError(), if there were no errors, and an error otherwise
   */
  def finalResult: CheckerResult = {
    _result match {
      case NoError() =>
        if (_nFoundErrors > 0) {
          Error(_nFoundErrors)
        } else {
          NoError()
        }

      case _ =>
        _result
    }
  }

  /**
   * Does the state of the state machine allow to continue the search.
   *
   * @return true, if the search may continue
   */
  def canContinue: Boolean = {
    _result match {
      case NoError() => true
      case _         => false
    }
  }

  /**
   * Register a checking result.
   *
   * @param result a result of checking an invariant or a property
   */
  def onResult(result: CheckerResult): Unit = {
    result match {
      case Error(_) =>
        _nFoundErrors += 1
        if (_nFoundErrors >= params.nMaxErrors) {
          // go to an error state, as the maximum number of errors has been reached
          _result = Error(_nFoundErrors)
        } else {
          // the search may continue, to discover more errors
          _result = NoError()
        }

      case Deadlock() =>
        if (_nFoundErrors > 0) {
          // this deadlock is probably caused by exclusion of previous counterexamples, so it may be a false positive
          _result = Error(_nFoundErrors)
        } else {
          _result = Deadlock()
        }

      case _ =>
        _result = result
    }
  }
}
