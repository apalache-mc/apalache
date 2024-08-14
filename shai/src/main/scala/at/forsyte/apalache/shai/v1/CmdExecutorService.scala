package at.forsyte.apalache.shai.v1

import java.io.{PrintWriter, StringWriter}
import scala.util.Try
import com.typesafe.scalalogging.Logger
import io.grpc.Status
import zio.ZEnv
import zio.ZIO
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.{Pass, PassChainExecutor}
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.shai.v1.cmdExecutor.{
  Cmd, CmdError, CmdErrorType, CmdRequest, CmdResponse, PingRequest, PongResponse, ZioCmdExecutor,
}
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.passes.imp.ParserModule
import at.forsyte.apalache.tla.passes.typecheck.TypeCheckerModule
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.io.annotations.PrettyWriterWithAnnotations
import at.forsyte.apalache.io.annotations.store._

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

  /** No-op RPC used to check the connection */
  def ping(req: PingRequest): Result[PongResponse] = ZIO.succeed(PongResponse())

  def run(req: CmdRequest): Result[CmdResponse] = for {
    cmd <- validateCmd(req.cmd)
    resp <- executeCmd(cmd, req.config) match {
      case Left(err) => ZIO.succeed(CmdResponse.Result.Failure(err))
      case Right(r)  => ZIO.succeed(CmdResponse.Result.Success(r.toString()))
    }
  } yield CmdResponse(resp)

  // Convert pass error results into the JSON representation
  private object Converters {
    import ujson._

    def passErr(err: Pass.PassFailure): CmdError = {
      CmdError(errorType = CmdErrorType.PASS_FAILURE, data = ujson.write(err))
    }

    def throwableErr(err: Throwable): CmdError = {
      val errData = Obj("msg" -> err.getMessage(), "stack_trace" -> err.getStackTrace().map(_.toString()).toList)
      CmdError(errorType = CmdErrorType.UNEXPECTED, data = ujson.write(errData))
    }

    // When sequencing the setup and execution of commands, any `Failure(v : Throwable)` can be automatically converted into
    // into a `CmdError` via `throwableErr`
    implicit class TryCmdErr[O](v: Try[O]) {
      def toCmdResult: Either[CmdError, O] = v.toEither.left.map(throwableErr)
    }
  }

  import Converters._
  private def executeCmd(cmd: Cmd, cfgStr: String): Either[CmdError, ujson.Value] = {

    for {
      cfg <- ConfigManager(cfgStr).map { cfg =>
        cfg.copy(common = cfg.common.copy(command = Some("server")))
      }.toCmdResult

      toolModule <- {
        import OptionGroup._
        cmd match {
          case Cmd.PARSE | Cmd.TLA => WithIO(cfg).map(new ParserModule(_)).toCmdResult
          case Cmd.CHECK           => WithCheckerPreds(cfg).map(new CheckerModule(_)).toCmdResult
          case Cmd.TYPECHECK       => WithTypechecker(cfg).map(new TypeCheckerModule(_)).toCmdResult
          case Cmd.Unrecognized(_) =>
            throw new IllegalArgumentException("programmer error: executeCmd applied before validateCmd")
        }
      }

      tlaModule <-
        try { PassChainExecutor.run(toolModule).left.map(passErr) }
        catch {
          case err: Throwable => Left(throwableErr(err))
        }
    } yield cmd match {
      case Cmd.TLA => tlaModuleToJsonString(tlaModule)
      case _       => TlaToUJson(tlaModule)
    }
  }

  private def tlaModuleToJsonString(module: TlaModule): ujson.Value = {
    val annotationStore = createAnnotationStore()

    val buf = new StringWriter()
    val prettyWriter = new PrettyWriterWithAnnotations(annotationStore, new PrintWriter(buf))
    val modules_to_extend = List("Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants")
    prettyWriter.write(module, modules_to_extend)
    val moduleString = buf.toString()

    val modifiedModule = extractLetFromFolds(moduleString)
    ujson.Str(modifiedModule)
  }

  // Apalache inlines fold operator arguments as LET .. IN expressions, but this
  // is not valid for SANY. In order to produce a valid TLA+ module from Quint
  // files, we transform expressions like:
  // ```
  // ApaFoldSet(LET __QUINT_LAMBDAn(a, b) == c IN __QUINT_LAMBDAn, init, set)
  // ```
  //
  // into:
  // ```
  // LET __QUINT_LAMBDAn(a, b) == c IN ApaFoldSet(__QUINT_LAMBDAn, init, set)
  // ```
  private def extractLetFromFolds(module: String): String = {
    val regex = """(?s)(ApaFold[\w]*\()\s*(LET\s.*?\sIN\s+)(__QUINT_LAMBDA)"""
    return module.replaceAll(regex, "$2 $1$3")
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
