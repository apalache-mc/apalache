package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.tla.bmcmt.{arraysEncoding, oopsla19Encoding, SMTEncoding}
import org.backuity.clist._
import org.backuity.clist.util.Read

/**
 * This command initiates the 'check' command line.
 *
 * @author
 *   Igor Konnov
 */
class CheckCmd(name: String = "check", description: String = "Check a TLA+ specification")
    extends AbstractCheckerCmd(name, description) with General {

  // Parses the smtEncoding option
  implicit val smtEncodingRead: Read[SMTEncoding] =
    Read.reads[SMTEncoding]("a SMT encoding, either oopsla19 or arrays") {
      case "arrays"        => arraysEncoding
      case "oopsla19"      => oopsla19Encoding
      case oddEncodingType => throw new IllegalArgumentException(s"Unexpected SMT encoding type $oddEncodingType")
    }

  var nworkers: Int = opt[Int](name = "nworkers", default = 1,
      description = "the number of workers for the parallel checker (soon), default: 1")
  var algo: String = opt[String](name = "algo", default = "incremental",
      description = "the search algorithm: offline, incremental, parallel (soon), default: incremental")
  var smtEncoding: SMTEncoding = opt[SMTEncoding](name = "smt-encoding", useEnv = true, default = oopsla19Encoding,
      description =
        s"the SMT encoding: ${oopsla19Encoding}, ${arraysEncoding} (experimental), default: ${oopsla19Encoding} (overrides envvar SMT_ENCODING)")
  var tuningOptionsFile: String =
    opt[String](name = "tuning-options-file", default = "",
        description = "filename of the tuning options, see docs/tuning.md")
  var tuningOptions: String =
    opt[String](name = "tuning-options", default = "",
        description =
          "tuning options as arguments in the format key1=val1:key2=val2:key3=val3 (priority over --tuning-options-file)")
  var discardDisabled: Boolean = opt[Boolean](name = "discard-disabled", default = true,
      description =
        "pre-check, whether a transition is disabled, and discard it, to make SMT queries smaller, default: true")
  var noDeadlocks: Boolean =
    opt[Boolean](name = "no-deadlock", default = false, description = "do not check for deadlocks, default: false")

  var maxError: Int =
    opt[Int](name = "max-error",
        description =
          "do not stop on first error, but produce up to a given number of counterexamples (fine tune with --view), default: 1",
        default = 1)

  var view: String =
    opt[String](name = "view", description = "the state view to use with --max-error=n, default: transition index",
        default = "")
}
