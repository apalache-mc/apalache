package at.forsyte.apalache.tla.tooling.opt

import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.shai
import org.backuity.clist._
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.OptionGroup
import com.github.apalachemc.apalache.jsonrpc.JsonRpcServerApp

import scala.util.Try

class ServerCmd extends ApalacheCommand(name = "server", description = "Run in server mode") with LazyLogging {

  var port: Option[Int] = opt[Option[Int]](
      description = "the port served by the RPC server, default: 8822 (overrides envvar PORT)", useEnv = true)

  var serverType: String = opt[String](
      description = "the type of server to run: 'checker' (shai-grpc) or 'explorer' (json-rpc), default: checker",
      default = "checker")

  override def toConfig(): Try[Config.ApalacheConfig] = {
    super.toConfig().map { cfg =>
      val selectedServerType = serverType.toLowerCase match {
        case "checker" => Config.CheckerServer()
        case "explorer"  => Config.ExplorerServer()
        case invalid   =>
          logger.warn(s"Invalid server type: $invalid, using default (checker)")
          Config.CheckerServer()
      }
      cfg.copy(server = Config.Server(port, serverType = selectedServerType))
    }
  }

  def run(): Right[Nothing, String] = {
    val cfg = configuration.get
    val options = OptionGroup.WithServer(cfg).get

    logger.info(s"Starting ${options.server.serverType} server on port ${options.server.port}...")
    options.server.serverType match {
      case Config.CheckerServer() =>
        val server = shai.v1.RpcServer(options.server.port)
        server.main(Array())
      case Config.ExplorerServer() =>
        JsonRpcServerApp.run(configuration, options.server.port)
    }

    Right("Server terminated")
  }
}
