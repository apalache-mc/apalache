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
import io.grpc.Status
import zio.{Ref, UIO, ZEnv, ZIO}
import java.util.UUID

// TODO The connnection type will become enriched with more structure
// as we build out the server
private case class Conn(
    id: UUID)

/**
 * The service enabling interaction with the symbolic model checker, via the
 * [[at.forsyte.apalache.tla.bmcmt.trex.TransitionExecutor]]
 *
 * @param connections
 *   A thread-safe, mutable reference holding a map registering connections by their unique ID
 */
class TransExplorerService(connections: Ref[Map[UUID, Conn]]) extends ZioTransExplorer.ZTransExplorer[ZEnv, Any] {

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

  private def addConnection(c: Conn): UIO[Unit] = connections.update(_ + (c.id -> c))
}
