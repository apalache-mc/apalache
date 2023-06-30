package at.forsyte.apalache.shai.v1

import zio.{console, Ref, ZEnv, ZIO}

import java.util.UUID
import scalapb.zio_grpc.ServerMain
import scalapb.zio_grpc.ServiceList
import com.typesafe.scalalogging.LazyLogging
import io.grpc.ServerBuilder

/**
 * The Shai RPC server handling gRPC requests to interact with the model checker
 *
 * We extend LazyLogging to give the server process access to the same logger configured for the rest of Apalache.
 */
class RpcServer(override val port: Int) extends ServerMain with LazyLogging {
  override def welcome: ZIO[ZEnv, Throwable, Unit] =
    console.putStrLn(s"The Apalache server is running on port ${port}. Press Ctrl-C to stop.")

  val createTransExplorerService = for {
    // A thread safe mutable reference to the active connections
    // See https://zio.dev/version-1.x/datatypes/concurrency/ref/
    connections <- Ref.make(Map[UUID, Conn]())
    // Ensure atomic access to the parser
    // See https://github.com/informalsystems/apalache/issues/1114#issuecomment-1180534894
  } yield new TransExplorerService(connections, logger)

  val createCmdExecutorService = ZIO.succeed(new CmdExecutorService(logger))

  def services: ServiceList[ZEnv] =
    ServiceList.addM(createTransExplorerService).addM(createCmdExecutorService)

  // Enable existential types; builder's signature below cannot be expressed using wildcards.
  // This is needed even if the type below is omitted / inferred.
  import scala.language.existentials

  // Double max inbound message size to 8MB
  // Fixes `io.grpc.StatusRuntimeException: RESOURCE_EXHAUSTED: gRPC message exceeds maximum size`:
  // https://github.com/informalsystems/apalache/issues/2622
  override def builder: (x0) forSome { type x0 <: ServerBuilder[x0] } =
    super.builder.maxInboundMessageSize(8 * 1024 * 1024)
}

object RpcServer {
  val DEFAULT_PORT = 8822

  def apply(port: Int = DEFAULT_PORT) = new RpcServer(port)
}
