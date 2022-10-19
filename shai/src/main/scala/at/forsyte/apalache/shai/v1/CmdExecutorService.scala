package at.forsyte.apalache.shai.v1

import scala.util.Try
import com.typesafe.scalalogging.Logger
import io.grpc.Status
import zio.ZEnv
import zio.ZIO
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.{Pass, PassChainExecutor}
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.shai.v1.cmdExecutor.{Cmd, CmdRequest, CmdResponse, PingRequest, PongResponse, ZioCmdExecutor}
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.passes.imp.ParserModule
import at.forsyte.apalache.tla.passes.typecheck.TypeCheckerModule

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
      case Right(r)  => ZIO.succeed(CmdResponse.Result.Success(r.toString()))
      case Left(err) => ZIO.succeed(CmdResponse.Result.Failure(err.toString()))
    }
  } yield CmdResponse(resp)

  // Convert pass error results into the JSON representation
  private object Converters {
    import ujson._

    def passErr(err: Pass.PassFailure): ujson.Value = {
      Obj("error_type" -> "pass_failure", "data" -> err)
    }

    def throwableErr(err: Throwable): ujson.Value =
      Obj("error_type" -> "unexpected",
          "data" -> Obj("msg" -> err.getMessage(), "stack_trace" -> err.getStackTrace().map(_.toString()).toList))

    def convErr[O](v: Try[O]): Either[ujson.Value, O] = v.toEither.left.map(throwableErr)
  }

  /** No-op RPC used to check the connection */
  def ping(req: PingRequest): Result[PongResponse] = ZIO.succeed(PongResponse())

  import Converters._
  private def executeCmd(cmd: Cmd, cfgStr: String): Either[ujson.Value, ujson.Value] = {

    for {
      cfg <- convErr(ConfigManager(cfgStr)).map(cfg => cfg.copy(common = cfg.common.copy(command = Some("server"))))

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
        try { PassChainExecutor.run(toolModule).left.map(passErr) }
        catch {
          case err: Throwable => Left(throwableErr(err))
        }
    } yield TlaToUJson(tlaModule)
  }

  // Allows us to handle invalid protobuf messages on the ZIO level, before
  // passing the `cmd` to a sequence in the `Either` monad.
  private def validateCmd(cmd: Cmd): Result[Cmd] = cmd match {
    case Cmd.Unrecognized(_) =>
      val msg = s"Invalid protobuf value for Cmd enum: ${cmd}"
      ZIO.fail(Status.INVALID_ARGUMENT.withDescription(msg))
    case cmd => ZIO.succeed(cmd)
  }
}
