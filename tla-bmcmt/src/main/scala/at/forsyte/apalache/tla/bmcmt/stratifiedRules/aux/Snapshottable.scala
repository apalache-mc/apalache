package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

/**
 * An object, the state of which can be saved in a stack-like manner by `snapshot` and later restored by `revert`,
 * similar to an SMT context. This trait is used for: SMT contexts and value caches.
 *
 * @author
 *   Jure Kukovec
 */
trait Snapshottable {

  /**
   * Get the current level, that is the difference between the number of snapshots and reverts made so far.
   *
   * @return
   *   the current level, always non-negative.
   */
  def level: Int

  /**
   * Save the current state for a later recovery with `revert`. Increases level by 1.
   */
  def snapshot(): Unit

  /**
   * Discard all entries added at the current level. Decreases level by 1.
   *
   * Importantly, `revert` may be called multiple times and thus it is not sufficient to save only the latest state.
   */
  def revert(): Unit

  /**
   * Revert n times.
   * @param n
   *   Revert n times, if n > 0, otherwise, do nothing
   */
  def revert(n: Int): Unit

  /**
   * Clean the state completely.
   */
  def dispose(): Unit
}
