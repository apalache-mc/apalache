package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
 * This command initiates the 'check' command line.
 *
 * @author Igor Konnov
 */
class CheckCmd extends Command(name = "check", description = "Check a TLA+ specification") with General {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var output: Option[String] = opt[Option[String]](name = "output",
      description = "file to which a possible counterexample will be written (.tla, .json, or .out), default: None")
  var nworkers: Int = opt[Int](name = "nworkers", default = 1,
      description = "the number of workers for the parallel checker (soon), default: 1")
  var algo: String = opt[String](name = "algo", default = "incremental",
      description = "the search algorithm: offline, incremental, parallel (soon), default: incremental")
  var smtEncoding: Option[String] = opt[Option[String]](name = "smt-encoding", useEnv = true,
      description =
        "the SMT encoding: oopsla19, arrays (experimental), default: oopsla19 (overrides envvar SMT_ENCODING)")
  var config: String = opt[String](name = "config", default = "",
      description = "configuration file in TLC format,\n" +
        "default: <file>.cfg, or none if <file>.cfg not present")
  var cinit: String = opt[String](name = "cinit", default = "",
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")
  var init: String = opt[String](name = "init", default = "",
      description = "the name of an operator that initializes VARIABLES,\n" +
        "default: Init")
  var next: String =
    opt[String](name = "next", default = "", description = "the name of a transition operator, default: Next")
  var inv: String =
    opt[String](name = "inv", default = "", description = "the name of an invariant operator, e.g., Inv")
  var length: Int =
    opt[Int](name = "length", default = 10, description = "maximal number of Next steps, default: 10")
  var tuning: String =
    opt[String](name = "tuning", default = "", description = "filename of the tuning options, see docs/tuning.md")
  var tuningOptions: String =
    opt[String](name = "tuning-options", default = "",
        description =
          "tuning options as arguments in the format key1=val1:key2=val2:key3=val3 (priority over --tuning)")
  var discardDisabled: Boolean = opt[Boolean](name = "discard-disabled", default = true,
      description =
        "pre-check, whether a transition is disabled, and discard it, to make SMT queries smaller, default: true")
  var noDeadlocks: Boolean =
    opt[Boolean](name = "no-deadlock", default = true, description = "do not check for deadlocks, default: true")

  var maxError: Int =
    opt[Int](name = "max-error",
        description =
          "do not stop on first error, but produce up to a given number of counterexamples (fine tune with --view), default: 1",
        default = 1)

  var view: String =
    opt[String](name = "view", description = "the state view to use with --max-error=n, default: transition index",
        default = "")
}
