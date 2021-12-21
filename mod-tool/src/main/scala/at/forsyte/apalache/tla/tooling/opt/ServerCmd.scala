package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.Command

class ServerCmd
    extends Command(name = "server", description = "Run apalache in server mode (not yet supported)") with General {

  // Dummy file used for application (esp. output) configuration
  def file = new File("server")
}
