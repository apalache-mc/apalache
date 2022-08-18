package at.forsyte.apalache.tla.tooling.opt

import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.shai

class ServerCmd
    extends ApalacheCommand(name = "server", description = "Run in server mode (in early development)")
    with LazyLogging {

  def run() = {
    logger.info("Starting server...")
    shai.v1.RpcServer.main(Array())
    Right("Server terminated")
  }
}
