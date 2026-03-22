package at.forsyte.apalache.tla.bmcmt.trex
import at.forsyte.apalache.tla.bmcmt.InvariantKind
import at.forsyte.apalache.tla.bmcmt.rules.aux.Oracle
import at.forsyte.apalache.tla.lir.TlaEx

/**
 * A filtering transition executor. Keeps only transitions and invariants that match the regular expressions
 * `stepFilter` and `invFilter`, respectively.
 *
 * @param stepFilter
 *   a string that encodes a regular expression that recognizes pairs `\${stepNo}->\${transitionNo}`, where `\${stepNo}`
 *   is a step number and `\${transitionNo}` is a transition number. If empty, no filtering is applied.
 * @param invFilter
 *   a string that encodes a regular expression that recognizes triples `\${stepNo}->\${invariantKind}\${invariantNo}`,
 *   where `\${stepNo}` is a step number, `\${invariantKind}` is "state" or "action" (see [[InvariantKind]]), and
 *   `\${invariantNo}` is a invariant number. If empty, no filtering is applied.
 * @param trex
 *   the [[TransitionExecutor]] to delegate to
 * @tparam SnapshotT
 *   a snapshot type
 */
class FilteredTransitionExecutor[SnapshotT](stepFilter: String, invFilter: String, trex: TransitionExecutor[SnapshotT])
    extends TransitionExecutor[SnapshotT] {

  private val stepRe = stepFilter.r
  private val invRe = invFilter.r

  /**
   * Translate a transition into SMT and save it under the given number. This method returns false, if the transition
   * was found to be disabled during the translation. In this case, the translation result is still saved in the SMT
   * context. It is the user's responsibility to pop the context, e.g., by recovering from a snapshot. (In an
   * incremental solver, it is cheap; in an offline solver, this may slow down the checker.)
   *
   * Only keeps the transition if the word `\${stepNo}->\${transitionNo}` (where `\${stepNo}` is the current [[stepNo]]
   * and `\${transitionNo}` is the given `transitionNo`) is recognized by the regular expression `stepFilter`.
   *
   * @param transitionNo
   *   a number associated with the transition, must be unique for the current step
   * @param transitionEx
   *   the expression that encodes the transition, it must be a TLA+ action expression
   * @return
   *   true, if the transition has been successfully translated; false, if the translation has found that the transition
   *   is disabled
   */
  override def prepareTransition(transitionNo: Int, transitionEx: TlaEx): Boolean = {
    val word = s"$stepNo->$transitionNo"
    if (stepFilter.isEmpty || stepRe.pattern.matcher(word).matches) {
      trex.prepareTransition(transitionNo, transitionEx)
    } else {
      false
    }
  }

  /**
   * A syntactic test on whether a translated transition may change satisfiability of an assertion. It tests, whether
   * all variables mentioned in the assertion belong to the unchanged set of the transition.
   *
   * Only keeps the invariant if the word `\${stepNo}->\${invariantKind}\${invariantNo}` (where `\${stepNo}` is the
   * current [[FilteredTransitionExecutor.stepNo]], and `\${invariantKind}` and `\${transitionNo}` are the given
   * parameters) is recognized by the regular expression `invFilter`.
   *
   * @param transitionNo
   *   the index of a previously prepared transition
   * @param invariantKind
   *   the kind of assertion being tested
   * @param invariantNo
   *   an index identifying the tested assertion among those of the same `invariantKind`
   * @param assertion
   *   a state expression
   * @return
   *   true, if the transition may affect satisfiability of the assertion
   */
  override def mayChangeAssertion(
      transitionNo: Int,
      invariantKind: InvariantKind,
      invariantNo: Int,
      assertion: TlaEx): Boolean = {
    // string expressions identifying the invariant in the current and previous transitions
    val thisWord = s"$stepNo->$invariantKind$invariantNo"
    val prevWord = s"${stepNo - 1}->$invariantKind$invariantNo"
    // check exclusion by the transition filter
    val prevExcluded = (stepNo > 0) && invFilter.nonEmpty && !invRe.pattern.matcher(prevWord).matches
    val thisExcluded = invFilter.nonEmpty && !invRe.pattern.matcher(thisWord).matches
    // check if the current transition may change the assertion
    val mayChange = trex.mayChangeAssertion(transitionNo, invariantKind, invariantNo, assertion)
    // Unless the invariant is excluded at the current step, it may change satisfiability if:
    // 1. The assertion was excluded at the previous step (it may have changed then), or
    // 2. The current transition may change satisfiability.
    !thisExcluded && (prevExcluded || mayChange)
  }

  ///////////////////////////////////// delegate to the underlying implementation

  /**
   * The step that is currently encoded. Step 0 is reserved for CONSTANTS and the Init predicate. The transitions from
   * Next should be applied to steps 1, 2, ...
   */
  override def stepNo: Int = trex.stepNo

  /**
   * Retrieve the translated symbolic execution
   *
   * @return
   *   the accumulated execution
   */
  override def execution: EncodedExecution = trex.execution

  /**
   * Assume that a previously prepared transition fires. Use this method to check, whether a prepared transition is
   * enabled. This method should be called after prepareTransition.
   *
   * @param transitionNo
   *   the index of a previously prepared transition
   */
  override def assumeTransition(transitionNo: Int): Unit = trex.assumeTransition(transitionNo)

  /**
   * Evaluate a TLA+ expression against the current SMT model.
   *
   * @param timeoutSec
   *   timeout in seconds to evaluate the expression
   * @param expr
   *   an expression that refers to constants and/or state variables
   * @return
   *   the evaluated expression that refers to constants only
   */
  override def evaluate(timeoutSec: Int, expr: TlaEx): Option[TlaEx] = {
    trex.evaluate(timeoutSec, expr)
  }

  /**
   * Push an assertion about the current controlState.
   *
   * @param assertion
   *   a Boolean-valued TLA+ expression, usually a controlState expression, though it may be an action expression.
   */
  override def assertState(assertion: TlaEx): Unit = trex.assertState(assertion)

  /**
   * Initialize CONSTANTS by applying assignments within a given expression.
   *
   * @param constInit
   *   a constant initializer that contains assignments to primed constants.
   */
  override def initializeConstants(constInit: TlaEx): Unit = {
    trex.initializeConstants(constInit)
  }

  /**
   * Pick non-deterministically one transition among the transitions that are prepared in the current step. Further,
   * assume that the picked transition has fired. This method must be called after at least one call to
   * prepareTransition.
   */
  override def pickTransition(): Oracle = trex.pickTransition()

  /**
   * Get the numbers of prepared transitions.
   *
   * @return
   *   a sequence of numbers
   */
  override def preparedTransitionNumbers: Set[Int] = {
    trex.preparedTransitionNumbers
  }

  /**
   * Advance symbolic execution by renaming primed variables to non-primed. This method must be called after
   * pickTransition.
   */
  override def nextState(): Unit = trex.nextState()

  /**
   * Check, whether the current context of the symbolic execution is satisfiable.
   *
   * @param timeoutSec
   *   timeout in seconds
   * @return
   *   Some(true), if the context is satisfiable; Some(false), if the context is unsatisfiable; None, if the solver
   *   timed out or reported *unknown*.
   */
  override def sat(timeoutSec: Int): Option[Boolean] = trex.sat(timeoutSec)

  /**
   * Take a snapshot and return it
   *
   * @return
   *   the snapshot
   */
  override def snapshot(): ExecutionSnapshot[SnapshotT] = trex.snapshot()

  /**
   * Recover a previously saved snapshot (not necessarily saved by this object).
   *
   * @param shot
   *   a snapshot
   */
  override def recover(shot: ExecutionSnapshot[SnapshotT]): Unit = trex.recover(shot)

  /**
   * Decode the current symbolic execution
   *
   * @return
   *   the decoded execution
   */
  override def decodedExecution(): DecodedExecution = trex.decodedExecution()

  /**
   * Dispose the transition executor together with its context.
   */
  override def dispose(): Unit = trex.dispose()
}
