package at.forsyte.apalache.shai.v1

import at.forsyte.apalache.infra.passes.{Pass, PassChainExecutor}
import at.forsyte.apalache.io.OutputWorkspace
import at.forsyte.apalache.io.annotations.PrettyWriterWithAnnotations
import at.forsyte.apalache.io.annotations.store._
import at.forsyte.apalache.io.config.Constants.SERVER
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigResolver, ConfigParseResult, RemoteConfigValidator}
import at.forsyte.apalache.io.json.ujsonimpl.TlaToUJson
import at.forsyte.apalache.shai.v1.cmdExecutor._
import at.forsyte.apalache.tla.bmcmt.config.CheckerModule
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.tla.passes.imp.ParserModule
import at.forsyte.apalache.tla.passes.typecheck.TypeCheckerModule
import com.typesafe.scalalogging.Logger
import io.grpc.Status
import zio.{ZEnv, ZIO}

import java.io.{BufferedWriter, StringWriter}
import scala.util.Try
import scala.util.Using

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
    cfg <- validateConfig(req.config)
    resp <- executeCmd(cmd, cfg) match {
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
      val errData = Obj("msg" -> err.getMessage, "stack_trace" -> err.getStackTrace.map(_.toString()).toList)
      CmdError(errorType = CmdErrorType.UNEXPECTED, data = ujson.write(errData))
    }

    // When sequencing the setup and execution of commands, any `Failure(v : Throwable)` can be automatically converted into
    // into a `CmdError` via `throwableErr`
    implicit class TryCmdErr[O](v: Try[O]) {
      def toCmdResult: Either[CmdError, O] = v.toEither.left.map(throwableErr)
    }

    /**
     * Adapts configuration loading and resolution results to the command executor's `Either` pipeline.
     *
     * Successful results expose their value. Failed results combine their diagnostics into an
     * `IllegalArgumentException`, which [[throwableErr]] reports as an `UNEXPECTED` command error.
     */
    implicit class ConfigParseResultCmdErr[O](result: ConfigParseResult[O]) {

      /** Return the configured value or its errors encoded as a command error. */
      def toCmdResult: Either[CmdError, O] =
        if (result.isSuccess) Right(result.requireValue())
        else {
          val message = result.errors.mkString("; ")
          Left(throwableErr(new IllegalArgumentException(message)))
        }
    }
  }

  import Converters._

  private def executeCmd(cmd: Cmd, cfg: ApalacheConfig): Either[CmdError, ujson.Value] = {

    for {
      initialization <- ApalacheConfigResolver.resolveCommandInitialization(cfg).toCmdResult
      outputWorkspace <- Try(new OutputWorkspace(initialization)).toCmdResult
      toolModule <- {
        cmd match {
          case Cmd.PARSE | Cmd.TLA =>
            ApalacheConfigResolver.resolveParse(cfg).toCmdResult.map(new ParserModule(_, outputWorkspace))
          case Cmd.CHECK =>
            ApalacheConfigResolver.resolveCheck(cfg).toCmdResult.map(new CheckerModule(_, outputWorkspace))
          case Cmd.TYPECHECK =>
            ApalacheConfigResolver.resolveTypecheck(cfg).toCmdResult.map(new TypeCheckerModule(_, outputWorkspace))
          case Cmd.Unrecognized(_) =>
            throw new IllegalArgumentException("programmer error: executeCmd applied before validateCmd")
        }
      }

      tlaModule <-
        try { PassChainExecutor(toolModule).run().left.map(passErr) }
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
    Using.resource(new BufferedWriter(buf)) { writer =>
      val prettyWriter = new PrettyWriterWithAnnotations(annotationStore, writer)
      val modules_to_extend = List("Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants")
      prettyWriter.write(module, modules_to_extend)
    }
    val moduleString = buf.toString

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

  /** Parse untrusted request JSON without configuration-file discovery and reject filesystem-capable fields. */
  private def validateConfig(config: String): Result[ApalacheConfig] = {
    val parsed = RemoteConfigValidator.parse(config)
    if (parsed.isSuccess) {
      ZIO.succeed(parsed.requireValue().withCommand(SERVER))
    } else {
      ZIO.fail(Status.INVALID_ARGUMENT.withDescription(parsed.errors.mkString("; ")))
    }
  }
}
