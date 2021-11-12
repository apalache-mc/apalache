package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
 * This command initiates the 'typecheck' command line.
 *
 * @author Igor Konnov
 */
class TypeCheckCmd
    extends Command(name = "typecheck", description = "Check types in a TLA+ specification") with General {

  var inferPoly: Boolean = opt[Boolean](name = "infer-poly", default = true,
      description = "allow the type checker to infer polymorphic types, default: true")

}
