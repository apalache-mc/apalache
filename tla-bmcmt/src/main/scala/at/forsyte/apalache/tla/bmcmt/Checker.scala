package at.forsyte.apalache.tla.bmcmt

object Checker {
  object Outcome extends Enumeration {
    val NoError, Error, Deadlock, RuntimeError, Interrupted = Value
  }
}

trait Checker {
  import Checker._

  def run(): Outcome.Value
}
