package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{arg, opt, Command}

import java.io.File

// Holds the minimal necessary info about a specification.
abstract class AbstractCheckerCmd(val name: String, description: String)
    extends Command(name, description) with General {
  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var config: String = opt[String](name = "config", default = "", description = "configuration file in TLC format")
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
}
