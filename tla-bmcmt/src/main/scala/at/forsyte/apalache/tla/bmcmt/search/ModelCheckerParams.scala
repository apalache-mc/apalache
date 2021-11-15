package at.forsyte.apalache.tla.bmcmt.search

import java.io.File
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
 * @author Igor Konnov
 */
class ModelCheckerParams(checkerInput: CheckerInput, val stepsBound: Int, val saveDirectory: File,
    tuningOptions: Map[String, String] = Map(), val debug: Boolean = true) {

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
   * A timeout upon which a transition is split in its own group.
   * This is the minimal timeout. The actual timeout is updated at every step using `search.split.timeout.factor`.
   * In our experiments, small timeouts lead to explosion of the search tree.
   */
  val jailTimeoutMinSec: Long =
    BigInt(tuningOptions.getOrElse("search.split.timeout.minimum", "1800")).toLong

  /**
   * At every step, the jail timeout for the next step is computed as `maxTime * factor / 100`,
   * where `maxTime` is the maximum checking time among all enabled or disabled transitions.
   */
  val jailTimeoutFactor: Long =
    BigInt(tuningOptions.getOrElse("search.split.timeout.factor", "200")).toInt

  /**
   * A timeout (in seconds) that indicates for how long an idle worker has to wait until splitting
   * an active tree node into two.
   */
  val idleTimeoutSec: Long =
    BigInt(tuningOptions.getOrElse("search.idle.timeout", "1800")).toLong

  /**
   * A timeout (in milliseconds) that indicates for how long an idle worker has to wait until splitting
   * an active tree node into two.
   */
  def idleTimeoutMs: Long = idleTimeoutSec * 1000

  val smtTimeoutSec: Long =
    BigInt(tuningOptions.getOrElse("search.smt.timeout", "0")).toLong

  /**
   * The SMT encoding to be used.
   */
  var smtEncoding: String = ""

  // does the transition number satisfy the given filter at the given step?
  def stepMatchesFilter(stepNo: Int, transitionNo: Int): Boolean = {
    if (transitionFilter.length <= stepNo) {
      true // no filter applied
    } else {
      transitionNo.toString.matches("^%s$".format(transitionFilter(stepNo)))
    }
  }

}
