package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import org.backuity.clist.Command

class ClientCmd extends Command(name = "client", description = "Run client (not yet supported)") with General {

  // Dummy file used for application (esp. output) configuration
  def file = new File("client")
}
