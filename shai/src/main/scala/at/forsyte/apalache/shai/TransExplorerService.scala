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

private case class ParsingFailed(msg: String) extends Exception(msg)

/**
 * The service enabling interaction with the symbolic model checker, via the
 * [[at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutor]]
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

  /** Concurrent tasks performed by the service that produce values of type [[T]] */
  type Result[T] = ZIO[ZEnv, Status, T]

  /**
   * Creates and registers a new connection
   *
   * This method handles the OpenConnection RPC defined by `transExplorer.proto`
   *
   * @param req
   *   the request (isomorphic to the Unit)
   */
  def openConnection(req: ConnectRequest): Result[Connection] = for {
    id <- ZIO.effectTotal(UUID.randomUUID())
    _ <- addConnection(Conn(id))
  } yield Connection(id.toString())

  /**
   * Parses a spec into a model
   *
   * This method handles the [LoadModelRequest] RPC defined by `transExplorer.proto`
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
        ZIO.succeed(LoadModelResponse.Result.Err(err.getMessage()))
    }
  } yield LoadModelResponse(result)

  private def parseSpec(spec: String, aux: Seq[String]): Result[Either[Throwable, TlaModule]] =
    // Obtain permit on the semaphore protecting access to the parser, ensuring the parser is not
    // run by more than one thread at a time.
    parserSemaphore.withPermit(ZIO.effectTotal(try {
      val parser = Executor(new ParserModule)
      parser.passOptions.set("parser.source", SourceOption.StringSource(spec, aux))
      parser.run().left.map(code => ParsingFailed(s"Parsing failed with error code: ${code}"))
    } catch {
      case e: Throwable => Left(ParsingFailed(s"Parsing failed with exception: ${e.getMessage()}"))
    }))

  private def jsonOfModule(module: TlaModule): String = {
    new TlaToUJson(None).makeRoot(Seq(module)).toString
  }

  private def addConnection(c: Conn): Result[Unit] = connections.update(_ + (c.id -> c))

  private def getConnection(id: String): Result[Conn] = {
    for {
      uuid <-
        try {
          ZIO.succeed(UUID.fromString(id))
        } catch {
          case _: IllegalArgumentException =>
            // TODO log for invalid conn ID: https://github.com/informalsystems/apalache/issues/1849
            ZIO.fail(Status.INVALID_ARGUMENT)
        }
      connMap <- connections.get
      conn <- connMap.get(uuid) match {
        // TODO log for unregistered uuid
        case None    => ZIO.fail(Status.FAILED_PRECONDITION)
        case Some(c) => ZIO.succeed(c)
      }
    } yield conn
  }

  private def updateConnection(id: String)(f: Conn => Conn): Result[Conn] = for {
    conn <- getConnection(id)
    updatedConn = f(conn)
    _ <- addConnection(updatedConn)
  } yield updatedConn

}
