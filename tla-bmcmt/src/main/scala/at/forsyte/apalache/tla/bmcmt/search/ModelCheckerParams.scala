package at.forsyte.apalache.tla.bmcmt.search

import at.forsyte.apalache.io.config.{SMTEncoding, SearchKind}
import at.forsyte.apalache.tla.bmcmt.CheckerInput
import at.forsyte.apalache.tla.bmcmt.search.ModelCheckerParams.InvariantMode.{AfterJoin, BeforeJoin, InvariantMode}

object ModelCheckerParams {

  /**
   * The invariant checking mode. See tuning.md.
   */
  object InvariantMode extends Enumeration {
    type InvariantMode = Value
    val BeforeJoin, AfterJoin = Value
  }
}

/**
 * A collection of model checker parameters that come from the user configuration.
 *
 * @param stepsBound
 *   Step bound for bounded model-checking, excluding the initial transition introduced by `PrimingPass`. E.g.,
 *   `stepsBound=1` includes one actual application of the transition operator (e.g., `Next`)
 *
 * @author
 *   Igor Konnov
 */
class ModelCheckerParams(
    checkerInput: CheckerInput,
    val stepsBound: Int,
    tuningOptions: Map[String, String],
    val searchKind: SearchKind,
    val seed: Int,
    val maxRun: Int,
    val outputTraces: Boolean) {

  /**
   * If pruneDisabled is set to false, there will be no check of whether a transition is enabled.
   */
  var discardDisabled: Boolean = true

  /**
   * If checkForDeadlocks is true, then the model checker should find deadlocks.
   */
  var checkForDeadlocks: Boolean = true

  /**
   * The invariant checking mode. When it is equal to AfterJoin, the invariant is checked after joining all transitions
   * per step. When it is equal to BeforeJoin, the invariant is checked before joining all transitions.
   */
  var invariantMode: InvariantMode =
    if ("after" == tuningOptions.getOrElse("search.invariant.mode", "before")) AfterJoin else BeforeJoin

  /**
   * The set of CONSTANTS, which are special (rigid) variables, as they do not change in the course of execution.
   */
  val consts = Set(checkerInput.rootModule.constDeclarations.map(_.name): _*)

  /**
   * The set of VARIABLES.
   */
  val vars = Set(checkerInput.rootModule.varDeclarations.map(_.name): _*)

  val transitionFilter: String =
    tuningOptions.getOrElse("search.transitionFilter", "")

  val invFilter: String =
    tuningOptions.getOrElse("search.invariantFilter", "")

  /**
   * The number of counterexamples to produce. The default value is 1.
   */
  var nMaxErrors: Int = 1

  /**
   * The limit on a single SMT query. The default value is 0 (unlimited).
   */
  var timeoutSmtSec: Int = 0

  /**
   * The SMT encoding to be used.
   */
  var smtEncoding: SMTEncoding = SMTEncoding.OOPSLA19

}
