package at.forsyte.apalache.tla.tooling.opt

import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.shai
import org.backuity.clist._

import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.OptionGroup

class ServerCmd
    extends ApalacheCommand(name = "server", description = "Run in server mode (in early development)")
    with LazyLogging {

  var port = opt[Option[Int]](description = "the port served by the RPC server, default: 8822 (overrides envvar PORT)",
      useEnv = true)

  override def toConfig() = {
    super.toConfig().map { cfg =>
      cfg.copy(server = Config.Server(port))
    }
  }

  def run() = {
    val cfg = configuration.get
    val options = OptionGroup.WithServer(cfg).get

    logger.info(s"Starting server on port ${options.server.port}...")
    val server = shai.v1.RpcServer(options.server.port)
    server.main(Array())
    Right("Server terminated")
  }
}
