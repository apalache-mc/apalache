package at.forsyte.apalache.hai.v1

/**
 * Provides the the TransExplorer service
 *
 * ==Overview==
 *
 * TODO
 */

import at.forsyte.apalache.hai.v1.transExplorer.ZioTransExplorer
import at.forsyte.apalache.hai.v1.transExplorer.{ConnectRequest, Connection}
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
 *   A thread-safe mutable reference to a map used to register connections by their unique
 */
class TransExplorerService(connections: Ref[Map[UUID, Conn]]) extends ZioTransExplorer.ZTransExplorer[ZEnv, Any] {

  /**
   * Creates and registers a new connection
   *
   * @param req
   *   the request (isomorphic to the Unit)
   */
  def openConnection(req: ConnectRequest): ZIO[ZEnv, Status, Connection] = for {
    id <- ZIO.effectTotal(UUID.randomUUID())
    _ <- addConnection(Conn(id))
  } yield Connection(id.toString())

  // TODO Add scalafmt config to allign for comprehension arrows?
  private def addConnection(conn: Conn): UIO[Unit] = for {
    conns <- connections.get
    _ <- connections.set(conns + (conn.id -> conn))
  } yield ()

}
