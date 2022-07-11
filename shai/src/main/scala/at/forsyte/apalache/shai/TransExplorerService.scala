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
import scala.util.control.Exception
import zio.{Ref, ZEnv, ZIO}
import com.google.protobuf.struct.Struct
import at.forsyte.apalache.infra.ExitCodes

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

private case class ParsingFailed(code: ExitCodes.TExitCode) extends Exception(s"Parsing failed with error code ${code}")

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

  /**
   * Parses a spec into a model
   *
   * This method handles the [LoadModelRequest] RPC defined by `transExplorer.proto`
   *
   * @param req
   *   the request to load a model, including the root module spec and any auxiliar modules
   */
  def loadModel(req: LoadModelRequest): Result[LoadModelResponse] = for {
    parseResult <- parseSpec(req.spec, req.aux)
    result <- parseResult match {
      case Right(module) =>
        for {
          _ <- updateConnection(req.conn)(_.setModel(module))
        } yield LoadModelResponse.Result.Spec(structOfModule(module))
      case Left(err) =>
        ZIO.succeed(LoadModelResponse.Result.Err(err.getMessage()))
    }
  } yield LoadModelResponse(result)

  private def parseSpec(spec: String, aux: Seq[String]): Result[Either[Throwable, TlaModule]] = {
    ZIO.effectTotal(for {
      parser <- Exception.allCatch.either {
        val parser = Executor(new ParserModule)
        parser.passOptions.set("parser.source", SourceOption.StringSource(spec, aux))
        parser
      }
      result <- parser.run().left.map(ParsingFailed)
    } yield result)
  }

  private def structOfModule(module: TlaModule): Struct = {
    val json = new TlaToUJson(None).makeRoot(Seq(module)).toString
    Struct.parseFrom(json.getBytes())
  }

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
