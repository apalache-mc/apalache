package at.forsyte.apalache.tla.tooling.opt

import java.io.File
import org.backuity.clist.{Command, _}

class ClientCmd extends Command(name = "client", description = "Run client (not yet supported)") with General {

  // Dummy file used for application (esp. output) configuration
  def file = new File("client")

  // Arguments passed to
  var rest = args[Seq[String]](description = "arguments to the client (run with `help` for complete details)")
}
