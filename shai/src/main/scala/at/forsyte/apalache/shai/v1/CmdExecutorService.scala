package at.forsyte.apalache.shai.v1

import com.typesafe.scalalogging.Logger
import io.grpc.Status
import scala.util.Failure
import scala.util.Success
import zio.ZIO
import zio.ZEnv

import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.infra.passes.ToolModule
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.shai.v1.cmdExecutor.Cmd
import at.forsyte.apalache.shai.v1.cmdExecutor.{CmdRequest, CmdResponse, ZioCmdExecutor}
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer // Required as implicit parameter to JsonTlaWRiter
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.infra.passes.options.Config

/**
 * Provides the [[CmdExecutorService]]
 *
 * ==Overview==
 *
 * The [[CmdExecutorService]] exposes an RPC interface to execute Apalache's CLI subcommand, thus enabling clients to
 * utilize much of Apalache's CLI functionality with the benefit of structured configuration, input, and output and
 * avoiding the repeated startup costs of the JVM.
 *
 * [[CmdExecutorService]] is meant to be registered with the [[RpcServer]], and should not need to be used directly.
 */

class CmdExecutorService(logger: Logger) extends ZioCmdExecutor.ZCmdExecutor[ZEnv, Any] {

  val _todo = logger

  /** Concurrent tasks performed by the service that produce values of type `T` */
  type Result[T] = ZIO[ZEnv, Status, T]

  def run(req: CmdRequest): Result[CmdResponse] = for {
    cmd <- validateCmd(req.cmd)
    resp <-
      parseConfig(req.config).flatMap(parserModuleOfCmd(cmd)) match {
        case Right(parserModule) => runExecutor(parserModule)
        case Left(err)           => ZIO.succeed(CmdResponse.Result.Failure(err))
      }
  } yield CmdResponse(resp)

  // TODO Structure responses
  private def runExecutor[O <: OptionGroup](module: ToolModule[O]) = ZIO.effectTotal {
    try {
      val executor = Executor[O](module)
      executor.run() match {
        case Right(module) =>
          // TODO gather data for response and incorporate into JSON response
          val m = jsonOfModule(module)
          CmdResponse.Result.Success(s"Command succeeded ${m}")
        case Left(code) => CmdResponse.Result.Failure(s"Command failed with error code: ${code}")
      }
    } catch {
      case e: Throwable => CmdResponse.Result.Failure(s"Command failed with exception: ${e.getMessage()}")
    }
  }

  private def validateCmd(cmd: Cmd): Result[Cmd] = cmd match {
    case Cmd.Unrecognized(_) =>
      val msg = s"Invalid protobuf value for Cmd enum: ${cmd}"
      ZIO.fail(Status.INVALID_ARGUMENT.withDescription(msg))
    case cmd => ZIO.succeed(cmd)
  }

  private def parserModuleOfCmd(cmd: Cmd)(cfg: Config.ApalacheConfig): Either[String, ParserModule] = {
    val (tryOptions, toolModule) =
      cmd match {
        case Cmd.PARSE => (OptionGroup.WithIO(cfg), new ParserModule(_))
        case _         => throw new Exception("invalid: toolModuleOfCmd applied before validateCmd")
      }
    tryOptions.toEither.left
      .map(err => s"Configuration given to command does not satisfy requirements: ${err.getMessage()}")
      .map(toolModule)
  }

  private def parseConfig(data: String) = {
    ConfigManager(data) match {
      case Success(cfg) => Right(cfg.copy(common = cfg.common.copy(command = Some("server"))))
      case Failure(err) => Left(s"Invalid configuration data given to command: ${err.getMessage()}")
    }
  }

  // private def loadOptions[O <: OptionGroup](attempt: Try[O]) = attempt.toEither.left.map { err =>
  //   s"Configuration given to command does not satisfy requirements: ${err.getMessage()}"
  // }

  private def jsonOfModule(module: TlaModule): String = {
    new TlaToUJson(None).makeRoot(Seq(module)).toString
  }
}
