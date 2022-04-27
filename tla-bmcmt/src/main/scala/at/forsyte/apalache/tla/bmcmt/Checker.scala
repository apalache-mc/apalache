package at.forsyte.apalache.tla.bmcmt

object Checker {

  /**
   * The result of running the model checker.
   */
  sealed trait CheckerResult {

    /**
     * Whether this result shall be reported as success (`true`) or error (`false`).
     */
    val isOk: Boolean
  }

  case class NoError() extends CheckerResult {
    override def toString: String = "NoError"

    override val isOk: Boolean = true
  }

  case class Error(nerrors: Int) extends CheckerResult {
    override def toString: String = s"Error"

    override val isOk: Boolean = false
  }

  /**
   * An execution cannot be extended. We interpret it as a deadlock.
   */
  case class Deadlock() extends CheckerResult {
    override def toString: String = "Deadlock"

    override val isOk: Boolean = false
  }

  /**
   * An execution cannot be extended but the user does not want to see it as a deadlock.
   */
  case class ExecutionsTooShort() extends CheckerResult {
    override def toString: String = "ExecutionsTooShort"

    override val isOk: Boolean = true
  }

  case class Interrupted() extends CheckerResult {
    override def toString: String = "Interrupted"

    override val isOk: Boolean = false
  }

  case class RuntimeError() extends CheckerResult {
    override def toString: String = "RuntimeError"

    override val isOk: Boolean = false
  }
}

trait Checker {
  import Checker._

  def run(): CheckerResult
}
