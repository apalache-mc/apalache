package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
 * This command initiates the 'parse' command line.
 *
 * @author Igor Konnov
 */
class ParseCmd extends Command(name = "parse", description = "Parse a TLA+ specification and quit") with General {

  // TODO Move these options to base trait (IoCmd) that can be exteded by both check and parse
  var file: File = arg[File](description = "a file containing a TLA+ specification (.tla or .json)")
  var output: Option[String] = opt[Option[String]](name = "output",
      description = "filename where to output the parsed source (.tla or .json),\n" +
        "default: None")
}
