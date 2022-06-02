package at.forsyte.apalache.shai.v1

import zio.{console, Ref, ZEnv, ZIO}
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
  } yield new TransExplorerService(connections)

  def services: ServiceList[ZEnv] =
    ServiceList.addM(createService)
}
