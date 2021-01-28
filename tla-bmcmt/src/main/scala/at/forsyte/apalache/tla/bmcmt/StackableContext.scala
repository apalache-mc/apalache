package at.forsyte.apalache.tla.bmcmt

/**
  * A context whose state can be saved on the stack by push and later restored by pop,
  * similar to an SMT context. This trait is used for: SMT contexts and value caches.
  *
  * @author Igor Konnov
  */
trait StackableContext {
  /**
    * Get the current context level, that is the difference between the number of pushes and pops made so far.
    *
    * @return the current level, always non-negative.
    */
  def contextLevel: Int

  /**
    * Save the current context and push it on the stack for a later recovery with pop.
    */
  def push(): Unit

  /**
    * Pop the previously saved context. Importantly, pop may be called multiple times and thus it is not sufficient
    * to save only the latest context.
    */
  def pop(): Unit

  /**
    * Pop the context n times.
    * @param n pop n times, if n > 0, otherwise, do nothing
    */
  def pop(n: Int)

  /**
    * Clean the context
    */
  def dispose()
}
