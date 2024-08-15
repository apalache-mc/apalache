package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.tla.bmcmt.{Checker, Counterexample}
import scala.collection.mutable.ListBuffer

/**
 * The search state machine that is implemented by SeqModelChecker. This machine is simple when the model checker fails
 * on the first error. It becomes complex when multiple errors are allowed.
 *
 * @param params
 *   model checker parameters
 * @author
 *   Igor Konnov
 */
class SearchState(params: ModelCheckerParams) {

  import Checker._

  private var _result: CheckerResult = NoError()
  private var _nFoundErrors: Int = 0
  private var _nTimeouts: Int = 0
  private val _counterexamples: ListBuffer[Counterexample] = ListBuffer.empty
  private var _nRunsLeft: Int =
    if (params.isRandomSimulation) params.nSimulationRuns else 1

  /**
   * Get the number of errors that were found so far (excluding deadlocks and runtime errors).
   *
   * @return
   *   number of found errors
   */
  def nFoundErrors: Int = _nFoundErrors

  /**
   * Get the number of SMT timeouts that occurred in the search.
   *
   * @return
   *   number of timeouts
   */
  def nTimeouts: Int = _nTimeouts

  /**
   * Get the number of simulation runs to explore.
   *
   * @return
   *   the non-negative number of runs.
   */
  def nRunsLeft: Int = _nRunsLeft

  /**
   * Get the cumulative result of the machine.
   *
   * @return
   *   NoError(), if there were no errors, and an error otherwise
   */
  def finalResult: CheckerResult = {
    _result match {
      case NoError() =>
        if (_nFoundErrors > 0) {
          Error(_nFoundErrors, _counterexamples.toList)
        } else if (_nTimeouts > 0) {
          SmtTimeout(_nTimeouts)
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
   * @return
   *   true, if the search may continue
   */
  def canContinue: Boolean = {
    _result match {
      case NoError() => _nRunsLeft > 0
      case _         => false
    }
  }

  /**
   * Register a checking result.
   *
   * @param result
   *   a result of checking an invariant or a property
   */
  def onResult(result: CheckerResult): Unit = {
    result match {
      case Error(_, counterexamples) =>
        _nFoundErrors += 1
        _counterexamples.appendAll(counterexamples)
        if (_nFoundErrors >= params.nMaxErrors) {
          // go to an error state, as the maximum number of errors has been reached
          _result = Error(_nFoundErrors, _counterexamples.toList)
        } else {
          // the search may continue, to discover more errors
          _result = NoError()
        }

      case Deadlock(counterexample) =>
        if (_nFoundErrors > 0) {
          // this deadlock is probably caused by exclusion of previous counterexamples, so it may be a false positive
          _result = Error(_nFoundErrors, _counterexamples.toList)
        } else {
          _result = Deadlock(counterexample)
        }

      case SmtTimeout(nTimeouts) =>
        // we still continue the search, but report incompleteness in [[this.finalResult]].
        _nTimeouts += nTimeouts
        _result = NoError()

      case _ =>
        _result = result
    }
  }

  /**
   * Register that one run of a symbolic execution is over.
   */
  def onRunDone(): Unit = {
    _nRunsLeft -= 1
    if (_nRunsLeft > 0 && _result == ExecutionsTooShort()) {
      // The current execution (of random simulation) is too short. However, we can try other executions.
      _result = NoError()
    }
  }
}
