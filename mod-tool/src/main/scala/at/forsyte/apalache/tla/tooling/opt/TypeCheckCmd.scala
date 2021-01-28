package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
  * This command initiates the 'typecheck' command line.
  *
  * @author Igor Konnov
  */
class TypeCheckCmd
    extends Command(
      name = "typecheck",
      description = "Check types in a TLA+ specification"
    )
    with General {

  var file: File =
    arg[File](description = "a TLA+ specification (.tla or .json)")
}
