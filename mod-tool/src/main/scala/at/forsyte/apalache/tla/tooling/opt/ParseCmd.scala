package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
 * This command initiates the 'parse' command line.
 *
 * @author Igor Konnov
 */
class ParseCmd extends Command(name = "parse", description = "Parse a TLA+ specification and quit") with General {

  var file: File = arg[File](description = "a TLA+ specification (.tla or .json)")
  var output: Option[String] = opt[Option[String]](name = "output",
      description = "file to which the parsed source is written (.tla or .json), default: None")
}
