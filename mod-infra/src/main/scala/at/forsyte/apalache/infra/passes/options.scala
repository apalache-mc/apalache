package at.forsyte.apalache.infra.passes

/** Collects the passoptions supported for configuring Apalache's various passes */
object options {

  /**
   * Defines the SMT encoding options supported
   *
   * @author
   *   Shon Feder
   */
  sealed abstract class SMTEncoding

  object SMTEncoding {
    final case object OOPSLA19 extends SMTEncoding {
      override def toString: String = "oopsla19"
    }
    final case object Arrays extends SMTEncoding {
      override def toString: String = "arrays"
    }

    val ofString: String => SMTEncoding = {
      case "arrays"        => Arrays
      case "oopsla19"      => OOPSLA19
      case oddEncodingType => throw new IllegalArgumentException(s"Unexpected SMT encoding type $oddEncodingType")
    }
  }

  trait Tuning {}

  trait General {
    val tuning: Tuning
  }

  trait Checker {
    val nworkers: Int = 1
    val discardDisabled: Boolean = true
    val noDeadlocks: Boolean = false
    val algo: String = "incremental" // TODO: convert to case class
    val smtEncoding: SMTEncoding = SMTEncoding.Oopsla19
    val maxError: Int = 1
    val view: String = "" // TODO: convert to optional
  }

  trait Typechecker {}
}
