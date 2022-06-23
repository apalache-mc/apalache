package at.forsyte.apalache.tla.tooling.opt

import java.io.File

import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.shai

class ServerCmd
    extends ApalacheCommand(name = "server", description = "Run in server mode (in early development)")
    with LazyLogging {

  // Dummy file used for application (esp. output) configuration
  def file = new File("server")

  def run() = {
    logger.info("Starting server...")
    shai.v1.RpcServer.main(Array())
    Right("Server terminated")
  }
}
