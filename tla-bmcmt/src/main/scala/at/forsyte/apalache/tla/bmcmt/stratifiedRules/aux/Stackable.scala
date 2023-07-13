package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext

/**
 * An object, the state of which can be saved in a stack-like manner by push and later restored by pop, similar to an
 * SMT context. This trait is used for: SMT contexts and value caches.
 *
 * Some objects maintain a certain contract with the SMT solver, that is, they may add constraints to a
 * [[at.forsyte.apalache.tla.bmcmt.smt.SolverContext]] on demand.
 *
 * @author
 *   Jure Kukovec
 */
trait Stackable {

  /**
   * Get the current level, that is the difference between the number of pushes and pops made so far.
   *
   * @return
   *   the current level, always non-negative.
   */
  def level: Int

  /**
   * Save the current state and push it on the stack for a later recovery with pop. Increases level by 1.
   */
  def push(): Unit

  /**
   * Discard all entries added at the current level. Decreases level by 1.
   *
   * Importantly, pop may be called multiple times and thus it is not sufficient to save only the latest state.
   */
  def pop(): Unit

  /**
   * Pop n times.
   * @param n
   *   pop n times, if n > 0, otherwise, do nothing
   */
  def pop(n: Int): Unit

  /**
   * Clean the state completely.
   */
  def dispose(): Unit

  /** SMT constraints */

  /**
   * Add implementation-specific constraints for all entries added at `lvl` or later.
   */
  def addConstraintsFromLevel(ctx: SolverContext)(lvl: Int): Unit

  /**
   * Add constraints for all entries added at any level.
   */
  def addConstraints(ctx: SolverContext): Unit = addConstraintsFromLevel(ctx)(0)

  /**
   * Add constraints for all entries added at the current level.
   */
  def addConstraintsForCurrentLevel(ctx: SolverContext): Unit = addConstraintsFromLevel(ctx)(level)

}
