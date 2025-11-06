package at.forsyte.apalache.shai.v1

/**
 * Provides the [[TransExplorerService]]
 *
 * ==Overview==
 *
 * The [[TransExplorerService]] exposes an RPC interface to drive the
 * [[at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutor]], thus enabling clients engage with the symbolic model
 * checker interactively.
 *
 * [[TranExplorerService]] is meant to be registered with [[RpcServer]], and should not need to be used directly.
 */

import at.forsyte.apalache.shai.v1.transExplorer.{
  ConnectRequest, Connection, LoadModelRequest, LoadModelResponse, PingRequest, PongResponse, TransExplorerError,
  TransExplorerErrorType, ZioTransExplorer,
}
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer
import at.forsyte.apalache.tla.lir.TlaModule
import io.grpc.Status

import java.util.UUID
import zio.{Ref, ZEnv, ZIO}
import com.typesafe.scalalogging.Logger
import at.forsyte.apalache.infra.passes.options.OptionGroup
import at.forsyte.apalache.infra.passes.PassChainExecutor
import at.forsyte.apalache.io.json.impl.ujson.TlaToUJson
import at.forsyte.apalache.tla.passes.imp.ParserModule

// TODO The connection type will become enriched with more structure
// as we build out the server
private case class Conn(
    id: UUID,
    model: Option[TlaModule] = None) {

  def setModel(model: TlaModule): Conn = {
    // TODO: reset all other state of Conn
    this.copy(model = Some(model))
  }
}

// TODO: Link the TransitionExecutor once tla.bmcmt.trex is imported
/**
 * The service enabling interaction with the symbolic model checker, via the `TransitionExecutor`
 *
 * ==Overview==
 * The public methods of this class are handlers for the protobuf messages defined in `transExplorer.proto`. These
 * handlers implement RPC calls enabling interaction with the Apalache model checker.
 *
 * On a successful remote procedure call, a handler returns a value of type `[[Result]][T]`, were `T` is the type of the
 * protobuf message specified as the response for the given RPC.
 *
 * The type `[[Result]][T]` is an alias for `ZIO[ZEnv, Status, T]`, which is fallible promise to return a value of type
 * `T` computed in the environment `ZEnv`.
 *
 * ==Error handling==
 *
 * There are two kinds of errors that may be signled by the PRC handlers:
 *
 *   - '''Protocol-level errors''', which indicate a failure to communicate successfully with the RPC system. These are
 *     indicated by the `Status` error codes.
 *   - '''Application-level errors''', which indicate some erroneous outcome in the execution of an RPC that was
 *     successfully communicated and executed. These are indicated by `err` results in the protobuf message sent back in
 *     response.
 *
 * Examples of '''protocol-level errors''':
 *
 *   - a protobuf message is malformed
 *   - an uncaught exception crashes the server
 *   - a request doesn't contain a connection
 *
 * Examples of '''application-level errors''':
 *
 *   - a syntax error is found when trying to parse a spec
 *   - a type error is found when typechecking a spec
 *   - a counterexample to a specified property is found while model checking
 *
 * @param connections
 *   A thread-safe, mutable reference holding a map registering connections by their unique ID
 *
 * @param logger
 *   The logger used by the service
 */
class TransExplorerService(connections: Ref[Map[UUID, Conn]], logger: Logger)
    extends ZioTransExplorer.ZTransExplorer[ZEnv, Any] {

  /** Concurrent tasks performed by the service that produce values of type `T` */
  type Result[T] = ZIO[ZEnv, Status, T]

  // The type of the `conn` field carried by all requests (exception for the `ConnectRequest`)
  //
  // It should always be `Some(Connection)`, but gRPC does not support required
  // fields, so instead we have to validate that the connection is supplied for
  // any incoming requests.
  private type RequestConn = Option[Connection]

  // A private object to give us ZIO managed access to an external logger.
  //
  // We need to lift the calls to the logger into ZIO effects so they can be
  // managed by the ZIO schedular for concurrent execution. See the project documentation
  // in shai/README.md for tips and references on understanding effects in ZIO.
  private object Log {
    private def shaiMsg(conn: RequestConn, msg: String): String = {
      val connId = conn.map(_.id).getOrElse("NO_CONNECTION")
      s"[Shai:${connId}]: ${msg}"
    }
    def debug(conn: RequestConn, msg: String): Result[Unit] = ZIO.effectTotal(logger.debug(shaiMsg(conn, msg)))
    def info(conn: RequestConn, msg: String): Result[Unit] = ZIO.effectTotal(logger.info(shaiMsg(conn, msg)))
    def warn(conn: RequestConn, msg: String): Result[Unit] = ZIO.effectTotal(logger.warn(shaiMsg(conn, msg)))
    def error(conn: RequestConn, msg: String): Result[Unit] = ZIO.effectTotal(logger.error(shaiMsg(conn, msg)))
  }

  /** No-op RPC used to check the connection */
  def ping(req: PingRequest): Result[PongResponse] = ZIO.succeed(PongResponse())

  /**
   * Creates and registers a new connection
   *
   * This method handles the `openConnection` RPC defined by `transExplorer.proto`
   *
   * Every session that interacts with the server must begin by obtaining a [[transExplorer.Connection]], and every
   * subsequent request must include a `conn` field holding the [[transExplorer.Connection]].
   *
   * @param req
   *   the request (isomorphic to the Unit)
   */
  def openConnection(req: ConnectRequest): Result[Connection] = for {
    id <- ZIO.effectTotal(UUID.randomUUID())
    _ <- setConnection(Conn(id))
    connection = Connection(id.toString)
    _ <- Log.info(Some(connection), "New connection created")
  } yield connection

  /**
   * Parses a spec into a model
   *
   * This method handles the [[transExplorer.LoadModelRequest]] RPC defined by `transExplorer.proto`
   *
   * @param req
   *   the request to load a model, including the root module spec and any auxiliary modules
   */
  def loadModel(req: LoadModelRequest): Result[LoadModelResponse] = for {
    // Ensure we can get a connection for the request
    _ <- getConnection(req.conn)
    parseResult <- parseSpec(req.spec, req.aux)
    result <- parseResult match {
      case Right(module) =>
        for {
          _ <- updateConnection(req.conn)(_.setModel(module))
          json = jsonOfModule(module)
          _ <- Log.info(req.conn, "Specification parsed successfully")
        } yield LoadModelResponse.Result.Spec(json)
      case Left(err) =>
        for {
          _ <- Log.warn(req.conn, s"Specification parsing failed: ${err}")
        } yield LoadModelResponse.Result.Err(err)
    }
  } yield LoadModelResponse(result)

  private def parseSpec(spec: String, aux: Seq[String]): Result[Either[TransExplorerError, TlaModule]] =
    ZIO.effectTotal {
      try {
        // TODO: replace hard-coded options with options derived from CLI params
        val options = {
          import OptionGroup._
          WithIO(
              common = Common(
                  command = "server",
                  outDir = new java.io.File("."),
                  runDir = None,
                  debug = true,
                  smtprof = false,
                  writeIntermediate = false,
                  profiling = false,
                  features = Seq(),
              ),
              input = Input(SourceOption.StringSource(spec, aux)),
              output = Output(Some(new java.io.File("."))),
          )
        }
        PassChainExecutor(new ParserModule(options))
          .run()
          .left
          .map { err =>
            TransExplorerError(errorType = TransExplorerErrorType.PASS_FAILURE, data = ujson.write(err))
          }
      } catch {
        case err: Throwable =>
          val errData =
            ujson.Obj("msg" -> err.getMessage, "stack_trace" -> err.getStackTrace.map(_.toString()).toList)
          Left(TransExplorerError(errorType = TransExplorerErrorType.UNEXPECTED, data = errData.toString()))
      }
    }

  private def jsonOfModule(module: TlaModule): String = {
    new TlaToUJson(None).makeRoot(Seq(module)).toString
  }

  // Sets the connection [[c]] in the map of [[connections]] by assigning [[c.id -> c]]
  // If [[c]] does not already exist in [[connections]] it will be added, or if a previous
  // version of a connection with the same id is present, the value will be overwritten.
  private def setConnection(c: Conn): Result[Unit] = connections.update(_ + (c.id -> c))

  // Takes a [[RequestConn]] that should always hold a [[Connection]] with a valid UUID
  // and returns the internal [[Conn]] instance storing session data corresponding to the connection.
  //
  // It checks for the required presence of a valid Connection ID, as desribed
  // in the documentation of the [[TransExplorerService]] service, and returns a
  // protol-level error via the [[zio.Status]] if no valid connection is given.
  private def getConnection(reqConn: RequestConn): Result[Conn] = {
    for {
      uuid <-
        reqConn match {
          case Some(conn) =>
            try { ZIO.succeed(UUID.fromString(conn.id)) }
            catch {
              case _: IllegalArgumentException =>
                val msg = s"Invalid RPC request: Connection id ${conn.id} is not a valid UUID"
                Log.error(None, msg).andThen(ZIO.fail(Status.INVALID_ARGUMENT.withDescription(msg)))
            }
          case None => ZIO.fail(Status.INVALID_ARGUMENT.withDescription("Invalid RPC request: no Connection provided"))
        }
      connMap <- connections.get
      conn <- connMap.get(uuid) match {
        case None =>
          val msg = "Invalid Connection: no connection is registered for id ${uuid}"
          Log.error(None, msg).andThen(ZIO.fail(Status.FAILED_PRECONDITION.withDescription(msg)))
        case Some(c) => ZIO.succeed(c)
      }
    } yield conn
  }

  // Updates the [[Conn]] corresponding by the id in the [[reqConn]], using the update function [[f]]
  //
  // [[f]] must not change the id of the underlying connection.
  private def updateConnection(reqConn: RequestConn)(f: Conn => Conn): Result[Conn] = for {
    conn <- getConnection(reqConn)
    updatedConn = f(conn)
    _ <-
      // Bail if the contract is violated
      ZIO.succeed(require(conn.id == updatedConn.id, "invalid updateConnction: connectin ID has been changed"))
    _ <- setConnection(updatedConn)
  } yield updatedConn
}
