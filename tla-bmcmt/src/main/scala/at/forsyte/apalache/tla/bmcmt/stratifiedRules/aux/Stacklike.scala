package at.forsyte.apalache.tla.bmcmt.stratifiedRules.aux

/**
 * An object, the state of which can be saved in a stack-like manner by `push` and later restored by `pop`, similar to
 * an SMT context. This trait is used for: SMT contexts and value caches.
 *
 * @author
 *   Jure Kukovec
 */
trait Stacklike {

  /**
   * Get the current level, that is the difference between the number of pushes and pops made so far.
   *
   * @return
   *   the current level, always non-negative.
   */
  def level: Int

  /**
   * Save the current state for a later recovery with `pop`. Increases level by 1.
   */
  def push(): Unit

  /**
   * Discard all entries added at the current level. Decreases level by 1.
   *
   * Importantly, `pop` may be called multiple times and thus it is not sufficient to save only the latest state.
   */
  def pop(): Unit

  /**
   * Pop n times.
   * @param n
   *   Pop n times, if n > 0, otherwise, do nothing
   */
  def pop(n: Int): Unit

  /**
   * Clean the state completely.
   */
  def dispose(): Unit
}
