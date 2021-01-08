package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{Command, _}

/**
  * This command initiates the 'config' command line.
  *
  * @author Igor Konnov
  */
class ConfigCmd extends Command(name = "config",
  description = "Configure Apalache options") with General {

  var submitStats: Option[Boolean] = opt[Option[Boolean]](
    name = "submit-stats",
    description = "submit Apalache usage statistics to tlapl.us (shared with TLC and TLA+ Toolbox)")
}
