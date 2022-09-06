package at.forsyte.apalache.shai.v1

import at.forsyte.apalache.shai.v1.cmdExecutor.ZioCmdExecutor
import zio.ZEnv
import com.typesafe.scalalogging.Logger
import io.grpc.Status
import scala.util.Failure
import scala.util.Success
import zio.ZIO
import zio.duration._
import zio.{Semaphore, ZEnv}

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
import scala.util.Try
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

  // TODO This will be used when we start adding the RPC calls
  val _todo = logger

  /** Concurrent tasks performed by the service that produce values of type `T` */
  type Result[T] = ZIO[ZEnv, Status, T]

  def run(req: CmdRequest): Result[CmdResponse] = for {
    toolModule <- toolModuleOfCmd(req.cmd)
    resp <-
      parseConfig(req.config).flatMap(toolModule) match {
        case Right(cfg) => runExecutor(cfg)
        case Left(err)  => ZIO.succeed(CmdResponse.Result.Failure(err))
      }
  } yield CmdResponse(resp)

  // TODO make configurable
  private val timeoutDuration: Duration = 2.minute

  private val timeoutErr = Status.DEADLINE_EXCEEDED.withDescription(s"Timeout of ${timeoutDuration} exceeded")

  // TODO Structure responses
  // TODO Currently every pass msut be run with a semaphore due to the thread unsafety of parsing
  //      We should instead put a mutext into the parser directly
  private def runExecutor[O <: OptionGroup](module: ToolModule[O]) = for {
    result <- parserSemaphore
      .withPermit(ZIO.effectTotal(try {
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
      }))
      .disconnect
      .timeoutFail(timeoutErr)(timeoutDuration)
  } yield result

  private def toolModuleOfCmd(cmd: Cmd) = cmd match {
    case Cmd.PARSE =>
      ZIO.succeed((cfg: Config.ApalacheConfig) => loadOptions(OptionGroup.WithIO(cfg)).map(new ParserModule(_)))
    case Cmd.Unrecognized(_) => ZIO.fail(Status.INVALID_ARGUMENT.withDescription("Invalid value for cmd"))

  }

  private def parseConfig(data: String) = {
    ConfigManager(data) match {
      case Success(cfg) => Right(cfg.copy(common = cfg.common.copy(command = Some("server"))))
      case Failure(err) => Left(s"Invalid configuration data given to command: ${err.getMessage()}")
    }
  }

  private def loadOptions[O <: OptionGroup](attempt: Try[O]) = {
    attempt match {
      case Success(o)   => Right(o)
      case Failure(err) => Left(s"Configuration given to command does not satisfy requirements: ${err.getMessage()}")
    }
  }

  private def jsonOfModule(module: TlaModule): String = {
    new TlaToUJson(None).makeRoot(Seq(module)).toString
  }
}
