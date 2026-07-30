package at.forsyte.apalache.tla.tooling.opt

import at.forsyte.apalache.infra.ExitCodes.TExitCode
import com.typesafe.scalalogging.LazyLogging
import at.forsyte.apalache.shai
import org.backuity.clist._
import org.backuity.clist.util.Read
import at.forsyte.apalache.io.config.{
  ApalacheConfig, ApalacheConfigResolver, ConfigParseResult, ServerPatch, ServerType,
}
import com.github.apalachemc.apalache.jsonrpc.JsonRpcServerApp

class ServerCmd extends ApalacheCommand(name = "server", description = "Run in server mode") with LazyLogging {

  private val serverTypeDescriptions = List(
      s"'${ServerType.Checker.name}' (shai-grpc)",
      s"'${ServerType.Explorer.name}' (json-rpc)",
  ).mkString(", ")

  implicit val serverTypeRead: Read[ServerType] =
    Read.reads[ServerType](s"a server type: ${ServerType.values.mkString(", ")}")(ServerType.fromString)

  var port: Option[Int] = opt[Option[Int]](description = descriptionWithDefault(
          "the port served by the RPC server",
          configDefaults.server.port,
      ) + " (overrides envvar PORT)", useEnv = true)

  var serverType: Option[ServerType] = opt[Option[ServerType]](description = descriptionWithDefault(
          s"the type of server to run: $serverTypeDescriptions",
          configDefaults.server.serverType,
      ), default = None)

  override def toConfig: ConfigParseResult[ApalacheConfig] =
    mergeConfig(
        super.toConfig,
        ApalacheConfig(server = ServerPatch(port = port, serverType = serverType)),
    )

  override def run(config: ApalacheConfig): Either[(TExitCode, String), String] = {
    runWithOptions(ApalacheConfigResolver.resolveServer(config)) { options =>
      logger.info(s"Starting ${options.server.serverType} server on port ${options.server.port}...")
      options.server.serverType match {
        case ServerType.Checker =>
          val server = shai.v1.RpcServer(options.server.port)
          server.main(Array())
        case ServerType.Explorer =>
          JsonRpcServerApp.run(ConfigParseResult.success(config), options.server.port)
      }
      Right("Server terminated")
    }
  }
}
