package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
  * This command initiates the 'parse' command line.
  *
  * @author Igor Konnov
  */
class ParseCmd extends Command(name = "parse",
                               description = "Parse a TLA+ specification and quit") {

  var file: File = arg[File](description = "a file containing a TLA+ specification")
}
