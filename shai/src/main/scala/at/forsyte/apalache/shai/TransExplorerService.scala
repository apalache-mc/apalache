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
  ConnectRequest, Connection, LoadModelRequest, UninitializedModel, ZioTransExplorer,
}
import at.forsyte.apalache.infra.Executor
import at.forsyte.apalache.infra.passes.SourceOption
import at.forsyte.apalache.io.json.impl.TlaToUJson
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer // Required as implicit parameter to JsonTlaWRiter
import at.forsyte.apalache.tla.imp.passes.ParserModule
import at.forsyte.apalache.tla.lir.TlaModule
import io.grpc.Status
import java.util.UUID
import zio.{Ref, ZEnv, ZIO}
import com.google.protobuf.struct.Struct

// TODO The connnection type will become enriched with more structure
// as we build out the server
private case class Conn(
    id: UUID,
    model: Option[TlaModule] = None) {

  def setModel(model: TlaModule): Conn = {
    // TODO: reset all other state of Conn
    this.copy(model = Some(model))
  }
}

/**
 * The service enabling interaction with the symbolic model checker, via the
 * [[at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutor]]
 *
 * @param connections
 *   A thread-safe, mutable reference holding a map registering connections by their unique ID
 */
class TransExplorerService(connections: Ref[Map[UUID, Conn]]) extends ZioTransExplorer.ZTransExplorer[ZEnv, Any] {

  /** Concurrent tasks from the service that produce values of type [[T]] */
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

  // TODO replace return with either
  def loadModel(req: LoadModelRequest): Result[UninitializedModel] = for {
    // TODO
    parser <- ZIO.effectTotal(Executor(new ParserModule))
    _ <- ZIO.effectTotal(parser.passOptions.set("parser.source", SourceOption.StringSource(req.spec)))
    module <- ZIO
      .effectTotal(parser.run() match {
        case Right(module) => module
        // TODO Handle any possible thrown error to convert into left
        case Left(_) => throw new Exception("TODO")
      })
    _ <- updateConnection(req.conn)(_.setModel(module))
    json <- ZIO.effectTotal(new TlaToUJson(None).makeRoot(Seq(module)).toString)
    struct <- ZIO.effectTotal(Struct.parseFrom(json.getBytes()))
  } yield UninitializedModel(spec = Some(struct)) // TODO: obtain google.protobuf.Struct

  private def addConnection(c: Conn): Result[Unit] = connections.update(_ + (c.id -> c))

  private def getConnection(id: String): Result[Conn] = {
    for {
      uuid <-
        try {
          ZIO.succeed(UUID.fromString(id))
        } catch {
          case _: IllegalArgumentException =>
            // TODO log for invalid conn ID
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
