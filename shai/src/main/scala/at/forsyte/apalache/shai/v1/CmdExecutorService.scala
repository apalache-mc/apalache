package at.forsyte.apalache.shai.v1

import com.typesafe.scalalogging.Logger
import io.grpc.Status
import scala.util.Failure
import scala.util.Success
import zio.ZIO
import zio.ZEnv

import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer // Required as implicit parameter to JsonTlaWRiter
import at.forsyte.apalache.shai.v1.cmdExecutor.Cmd
import at.forsyte.apalache.shai.v1.cmdExecutor.{CmdRequest, CmdResponse, ZioCmdExecutor}
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.typecheck.passes.TypeCheckerModule
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

  val _todo = logger

  /** Concurrent tasks performed by the service that produce values of type `T` */
  type Result[T] = ZIO[ZEnv, Status, T]

  def run(req: CmdRequest): Result[CmdResponse] = for {
    cmd <- validateCmd(req.cmd)
    resp <- executeCmd(cmd, req.config) match {
      case Right(r)  => ZIO.succeed(CmdResponse.Result.Success(r))
      case Left(err) => ZIO.succeed(CmdResponse.Result.Failure(err))
    }
  } yield CmdResponse(resp)

  private def executeCmd(cmd: Cmd, cfgStr: String): Either[String, String] = {
    // Convert a Try into an `Either` with `Left` the message from a possible `Failure`.
    def convErr[O](v: Try[O]) = v.toEither.left.map(e => e.getMessage())

    for {
      cfg <- parseConfig(cfgStr)

      toolModule <- {
        import OptionGroup._
        cmd match {
          case Cmd.PARSE     => convErr(WithIO(cfg)).map(new ParserModule(_))
          case Cmd.CHECK     => convErr(WithCheckerPreds(cfg)).map(new CheckerModule(_))
          case Cmd.TYPECHECK => convErr(WithTypechecker(cfg)).map(new TypeCheckerModule(_))
          case Cmd.Unrecognized(_) =>
            throw new IllegalArgumentException("programmer error: executeCmd applied before validateCmd")
        }
      }

      tlaModule <-
        try { PassChainExecutor.run(toolModule).left.map(errCode => s"Command failed with error code: ${errCode}") }
        catch {
          case e: Throwable => Left(s"Command failed with exception: ${e.getMessage()}")
        }

      json = jsonOfModule(tlaModule)
    } yield s"Command succeeded ${json}"
  }

  // Allows us to handle invalid protobuf messages on the ZIO level, before
  // passing the `cmd` to a sequence in the `Either` monad.
  private def validateCmd(cmd: Cmd): Result[Cmd] = cmd match {
    case Cmd.Unrecognized(_) =>
      val msg = s"Invalid protobuf value for Cmd enum: ${cmd}"
      ZIO.fail(Status.INVALID_ARGUMENT.withDescription(msg))
    case cmd => ZIO.succeed(cmd)
  }

  private def parseConfig(data: String): Either[String, Config.ApalacheConfig] = {
    ConfigManager(data) match {
      case Success(cfg) => Right(cfg.copy(common = cfg.common.copy(command = Some("server"))))
      case Failure(err) => Left(s"Invalid configuration data given to command: ${err.getMessage()}")
    }
  }

  private def jsonOfModule(module: TlaModule): String = {
    new TlaToUJson(None).makeRoot(Seq(module)).toString
  }
}
