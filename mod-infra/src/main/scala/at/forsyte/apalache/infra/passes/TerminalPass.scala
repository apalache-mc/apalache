package at.forsyte.apalache.infra.passes

/**
  * This pass does nothing but it can be used to collect the output of the final pass.
  */
class TerminalPass extends Pass {

  /**
    * The pass name.
    *
    * @return the name associated with the pass
    */
  override def name: String = "Terminal"

  /**
    * Run the pass.
    *
    * @return true, if the pass was successful
    */
  override def execute(): Boolean = {
    true
  }

  /**
    * Get the next pass in the chain. What is the next pass is up
    * to the module configuration and the pass outcome.
    *
    * @return the next pass, if exists, or None otherwise
    */
  override def next(): Option[Pass] = {
    None
  }
}
