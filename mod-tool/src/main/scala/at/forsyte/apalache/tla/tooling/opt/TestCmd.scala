package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{Command, _}

import java.io.File

/**
 * This command initiates the 'test' command line.
 *
 * @author Igor Konnov
 */
class TestCmd extends Command(name = "test", description = "Quickly test a TLA+ specification") with General {

  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var before: String =
    arg[String](name = "before", description = "the name of an operator to prepare the test, similar to Init")
  var action: String =
    arg[String](name = "action", description = "the name of an action to execute, similar to Next")
  var assertion: String =
    arg[String](name = "assertion",
        description = "the name of an operator that should evaluate to true after executing `action`")
  var cinit: String = opt[String](name = "cinit", default = "",
      description = "the name of an operator that initializes CONSTANTS,\n" +
        "default: None")
}
