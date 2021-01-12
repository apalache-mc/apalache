package at.forsyte.apalache.tla.bmcmt.trex
import at.forsyte.apalache.tla.bmcmt.rules.aux.Oracle
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A transition executor that keeps only the steps and invariants, which are given by the regular expressions.
  *
  * @param stepFilter a string that encodes a regular expression that recognizes pairs "stepNo->transitionNo",
  *                   where stepNo is a step number and transitionNo is a transition number; may be empty
  * @param invFilter  a string that encodes a regular expression over step numbers; may be empty
  * @param trex an implementation to delegate to
  * @tparam SnapshotT a snapshot type
  */
class FilteredTransitionExecutor[SnapshotT](stepFilter: String,
                                            invFilter: String,
                                            trex: TransitionExecutor[SnapshotT])
  extends TransitionExecutor[SnapshotT] {

  private val stepRe = stepFilter.r()
  private val invRe = invFilter.r()


  /**
    * Translate a transition into SMT and save it under the given number. This method returns false,
    * if the transition was found to be disabled during the translation. In this case, the translation result
    * is still saved in the SMT context. It is user's responsibility to pop the context, e.g., by recovering from
    * a snapshot. (In an incremental solver, it is cheap; in an offline solver, this may slow down the checker.)
    *
    * @param transitionNo a number associated with the transition, must be unique for the current step
    * @param transitionEx the expression that encodes the transition, it must be a TLA+ action expression
    * @return true, if the transition has been successfully translated;
    *         false, if the translation has found that the transition is disabled
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
    * A syntactic test on whether a translated transition may change satisfiability of an assertion.
    * It tests, whether all variables mentioned in the assertion belong to the unchanged set of the transition.
    *
    * @param transitionNo the index of a previously prepared transition
    * @param assertion    a state expression
    * @return true, if the transition may affect satisfiability of the assertion
    */
  override def mayChangeAssertion(transitionNo: Int, assertion: TlaEx): Boolean = {
    val prevExcluded = (stepNo > 0) && invFilter.nonEmpty && !invRe.pattern.matcher("%d".format(stepNo - 1)).matches
    val thisExcluded = invFilter.nonEmpty && !invRe.pattern.matcher(s"$stepNo").matches
    val mayChange = trex.mayChangeAssertion(transitionNo, assertion)
    // One of the options is allowed, unless it is excluded at the current step:
    // 1. The assertion was excluded at the previous step, or
    // 2. The transition may have changed the assertion.
    !thisExcluded && (prevExcluded || mayChange)
  }

  ///////////////////////////////////// delegate to the underlying implementation

  /**
    * The step that is currently encoded. Step 0 is reserved for CONSTANTS and the Init predicate.
    * The transitions from Next should be applied to steps 1, 2, ...
    */
  override def stepNo: Int = trex.stepNo

  /**
    * Retrieve the translated symbolic execution
    *
    * @return the accumulated execution
    */
  override def execution: ReducedExecution = trex.execution

  /**
    * Assume that a previously prepared transition fires. Use this method to check,
    * whether a prepared transition is enabled.
    * This method should be called after prepareTransition.
    *
    * @param transitionNo the index of a previously prepared transition
    */
  override def assumeTransition(transitionNo: Int): Unit = trex.assumeTransition(transitionNo)

  /**
    * Push an assertion about the current controlState.
    *
    * @param assertion a Boolean-valued TLA+ expression, usually a controlState expression,
    *                  though it may be an action expression.
    */
  override def assertState(assertion: TlaEx): Unit = trex.assertState(assertion)

  /**
    * Initialize CONSTANTS by applying assignments within a given expression.
    *
    * @param constInit a constant initializer that contains assignments to primed constants.
    */
  override def initializeConstants(constInit: TlaEx): Unit = {
    trex.initializeConstants(constInit)
  }

  /**
    * Pick non-deterministically one transition among the transitions that are prepared
    * in the current step. Further, assume that the picked transition has fired.
    * This method must be called after at least one call to prepareTransition.
    */
  override def pickTransition(): Oracle = trex.pickTransition()

  /**
    * Get the numbers of prepared transitions.
    *
    * @return a sequence of numbers
    */
  override def preparedTransitionNumbers: Set[Int] = {
    trex.preparedTransitionNumbers
  }

  /**
    * Advance symbolic execution by renaming primed variables to non-primed.
    * This method must be called after pickTransition.
    */
  override def nextState(): Unit = trex.nextState()

  /**
    * Check, whether the current context of the symbolic execution is satisfiable.
    *
    * @param timeoutSec timeout in seconds
    * @return Some(true), if the context is satisfiable;
    *         Some(false), if the context is unsatisfiable;
    *         None, if the solver timed out or reported *unknown*.
    */
  override def sat(timeoutSec: Long): Option[Boolean] = trex.sat(timeoutSec)

  /**
    * Take a snapshot and return it
    *
    * @return the snapshot
    */
  override def snapshot(): ExecutorSnapshot[SnapshotT] = trex.snapshot()

  /**
    * Recover a previously saved snapshot (not necessarily saved by this object).
    *
    * @param shot a snapshot
    */
  override def recover(shot: ExecutorSnapshot[SnapshotT]): Unit = trex.recover(shot)

  /**
    * Decode the current symbolic execution
    *
    * @return the decoded execution
    */
  override def decodedExecution(): DecodedExecution = trex.decodedExecution()

  /**
    * Dispose the transition executor together with its context.
    */
  override def dispose(): Unit = trex.dispose()
}
