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

import at.forsyte.apalache.shai.v1.transExplorer.ZioTransExplorer
import at.forsyte.apalache.shai.v1.transExplorer.{ConnectRequest, Connection}
import at.forsyte.apalache.tla.lir.TlaModule
import io.grpc.Status
import java.util.UUID
import zio.{Ref, UIO, ZEnv, ZIO}

// TODO Decide on refined representation for `Transition` (see https://github.com/informalsystems/apalache/issues/1116)
// Consider this as an abstract type for now, the representation is TBD
case class Transition(val v: Int) extends AnyVal

/**
 * Represents a model with uninitialized constants
 */
trait UninitializedModel {

  /** The specification of the model */
  val spec: TlaModule

  /** The known available transitions */
  val transitions: List[Transition]
}

/**
 * A model that has had it's constants initialized
 */
trait InitializedModel extends UninitializedModel {
  val constInitPrimed: Map[String, TlaEx]
}

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
  def openConnection(req: ConnectRequest): ZIO[ZEnv, Status, Connection] = for {
    id <- ZIO.effectTotal(UUID.randomUUID())
    _ <- addConnection(Conn(id))
  } yield Connection(id.toString())

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
