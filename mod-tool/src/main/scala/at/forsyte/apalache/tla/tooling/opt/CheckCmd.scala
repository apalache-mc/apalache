package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.{Command, _}

/**
  * This command initiates the 'check' command line.
  *
  * @author Igor Konnov
  */
class CheckCmd extends Command(name = "check",
  description = "Check a TLA+ specification") with General {

  var file: File = arg[File](description = "a file containing a TLA+ specification")
  var init: String = opt[String](
    name = "init", default = "Init",
    description = "the name of an initializing operator, default: Init")
  var next: String = opt[String](
    name = "next", default = "Next",
    description = "the name of a transition operator, default: Next")
  var inv: Option[String] =
    opt[Option[String]](name = "inv", description = "the name of an invariant operator, e.g., Inv")
  var length: Int =
    opt[Int](name = "length", default = 10,
      description = "the bound on the computation length, default: 10")
}
