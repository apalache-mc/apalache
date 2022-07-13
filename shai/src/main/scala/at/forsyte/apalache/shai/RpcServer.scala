package at.forsyte.apalache.shai.v1

import zio.{console, Ref, Semaphore, ZEnv, ZIO}
import java.util.UUID
import scalapb.zio_grpc.ServerMain
import scalapb.zio_grpc.ServiceList

object RpcServer extends ServerMain {
  override def port: Int = 8822

  override def welcome: ZIO[ZEnv, Throwable, Unit] =
    console.putStrLn("The Apalache server is running. Press Ctrl-C to stop.")

  val createService = for {
    // A thread safe mutable reference to the active connections
    // See https://zio.dev/version-1.x/datatypes/concurrency/ref/
    connections <- Ref.make(Map[UUID, Conn]())
    // Ensure atomic access to the parser
    // See https://github.com/informalsystems/apalache/issues/1114#issuecomment-1180534894
    parserSemaphore <- Semaphore.make(permits = 1)
  } yield new TransExplorerService(connections, parserSemaphore)

  def services: ServiceList[ZEnv] =
    ServiceList.addM(createService)
}
