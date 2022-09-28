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

  object CheckerResult {

    import upickle.default.{writer, Writer}
    import ujson._

    implicit val ujsonView: CheckerResult => ujson.Value = { result =>
      val (errType, errData) = result match {
        case Error(nerrors, counterexamples) =>
          ("violation", Obj("counterexamples" -> counterexamples, "nerrors" -> nerrors))
        case Deadlock(counterexample) =>
          ("deadlock", Obj("counterexample" -> counterexample))
        case other => (other.toString(), Obj())
      }
      Obj("error_type" -> errType, "error_data" -> errData)
    }

    implicit val upickleWriter: Writer[CheckerResult] = writer[ujson.Value].comap(ujsonView)
  }

  case class NoError() extends CheckerResult {
    override def toString: String = "NoError"

    override val isOk: Boolean = true
  }

  case class Error(nerrors: Int, counterexamples: Seq[Counterexample]) extends CheckerResult {
    override def toString: String = s"Error"

    override val isOk: Boolean = false
  }

  /**
   * An execution cannot be extended. We interpret it as a deadlock.
   */
  case class Deadlock(counterexample: Option[Counterexample]) extends CheckerResult {
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
