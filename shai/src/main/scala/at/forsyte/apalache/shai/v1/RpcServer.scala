package at.forsyte.apalache.shai.v1

import zio.{console, Ref, ZEnv, ZIO}
import java.util.UUID
import scalapb.zio_grpc.ServerMain
import scalapb.zio_grpc.ServiceList
import com.typesafe.scalalogging.LazyLogging

/**
 * The Shai RPC server handling gRPC requests to interact with the model checker
 *
 * We extend LazyLogging to give the server process access to the same logger configured for the rest of Apalache.
 */
object RpcServer extends ServerMain with LazyLogging {
  override def port: Int = 8822

  override def welcome: ZIO[ZEnv, Throwable, Unit] =
    console.putStrLn("The Apalache server is running. Press Ctrl-C to stop.")

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
}
