package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.{Command, _}

/**
 * This command initiates the 'config' command line.
 *
 * @author Igor Konnov
 */
class ConfigCmd extends Command(name = "config", description = "Configure Apalache options") with General {

  var submitStats: Option[Boolean] = opt[Option[Boolean]](name = "enable-stats",
      description = "Let Apalache submit usage statistics to tlapl.us\n"
        + "(shared with TLC and TLA+ Toolbox)\nSee: https://apalache.informal.systems/docs/apalache/statistics.html")
}
