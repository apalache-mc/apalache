package at.forsyte.apalache.tla.bmcmt

object Checker {

  /**
   * The result of running the model checker.
   */
  sealed trait CheckerResult {}

  case class NoError() extends CheckerResult {
    override def toString: String = "NoError"
  }

  case class Error(nerrors: Int) extends CheckerResult {
    override def toString: String = s"Error"
  }

  case class Deadlock() extends CheckerResult {
    override def toString: String = "Deadlock"
  }

  case class Interrupted() extends CheckerResult {
    override def toString: String = "Interrupted"
  }

  case class RuntimeError() extends CheckerResult {
    override def toString: String = "RuntimeError"
  }
}

trait Checker {
  import Checker._

  def run(): CheckerResult
}
