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
  ConnectRequest, Connection, LoadModelRequest, LoadModelResponse, ZioTransExplorer,
}
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.infra.passes.SourceOption
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer // Required as implicit parameter to JsonTlaWRiter
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.lir.TlaModule
import io.grpc.Status
import java.util.UUID
import zio.{Ref, Semaphore, ZEnv, ZIO}
import zio.duration._

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
 * @param parserSemaphore
 *   A semaphore used to ensure atomic access to the SANY parser. This is necessitated by the statefull design of the
 *   SANY parser, which makes it impossible to run two instance of the parser concurrently in the same runtime. See
 *   https://github.com/informalsystems/apalache/issues/1114#issuecomment-1180534894 for details.
 */
class TransExplorerService(connections: Ref[Map[UUID, Conn]], parserSemaphore: Semaphore)
    extends ZioTransExplorer.ZTransExplorer[ZEnv, Any] {

  /** Concurrent tasks performed by the service that produce values of type `T` */
  type Result[T] = ZIO[ZEnv, Status, T]

  // The type of the `conn` field carried by all requests (exception for the `ConnectRequest`)
  //
  // It should always be `Some(Connection)`, but gRPC does not support required
  // fields, so instead we have to validate that the connection is supplied for
  // any incoming requests.
  private type RequestConn = Option[Connection]

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
  } yield Connection(id.toString())

  /**
   * Parses a spec into a model
   *
   * This method handles the [[transExplorer.LoadModelRequest]] RPC defined by `transExplorer.proto`
   *
   * @param req
   *   the request to load a model, including the root module spec and any auxiliary modules
   */
  def loadModel(req: LoadModelRequest): Result[LoadModelResponse] = for {
    parseResult <- parseSpec(req.spec, req.aux)
    result <- parseResult match {
      case Right(module) =>
        for {
          _ <- updateConnection(req.conn)(_.setModel(module))
          json = jsonOfModule(module)
        } yield LoadModelResponse.Result.Spec(json)
      case Left(err) =>
        ZIO.succeed(LoadModelResponse.Result.Err(err))
    }
  } yield LoadModelResponse(result)

  private val parserTimeoutDuration: Duration = 2.minute

  private def parseSpec(spec: String, aux: Seq[String]): Result[Either[String, TlaModule]] = for {
    // Obtain permit on the semaphore protecting access to the parser, ensuring the parser is not
    // run by more than one thread at a time.
    result <- parserSemaphore
      .withPermit(ZIO.effectTotal(try {
        val parser = Executor(new ParserModule)
        parser.passOptions.set("parser.source", SourceOption.StringSource(spec, aux))
        parser.run().left.map(code => s"Parsing failed with error code: ${code}")
      } catch {
        case e: Throwable => Left(s"Parsing failed with exception: ${e.getMessage()}")
      }))
      .disconnect
      .timeout(parserTimeoutDuration)
  } yield result.getOrElse(Left(s"Parsing failed with timeout: exceeded ${parserTimeoutDuration}"))

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
  // It provides error checking ont the required presence of a valid Connection
  // ID, as desribed in the documentation of the [[TransExplorerService]]
  // service.
  //
  // TODO Add logging for invalid conn ID: https://github.com/informalsystems/apalache/issues/1849
  // TODO Add loggin for unregistered conn ID: https://github.com/informalsystems/apalache/issues/1849
  private def getConnection(reqConn: RequestConn): Result[Conn] = {
    for {
      uuid <-
        reqConn match {
          case Some(conn) =>
            try { ZIO.succeed(UUID.fromString(conn.id)) }
            catch {
              case _: IllegalArgumentException =>
                ZIO.fail(
                    Status.INVALID_ARGUMENT.withDescription("Invalid RPC request: Connection id is not a valid UUID"))
            }
          case None => ZIO.fail(Status.INVALID_ARGUMENT.withDescription("Invalid RPC request: no Connection provided"))
        }
      connMap <- connections.get
      conn <- connMap.get(uuid) match {
        case None =>
          ZIO.fail(Status.FAILED_PRECONDITION.withDescription(
                  "Invalid Connection: no Connextion is registered for given ID"))
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
