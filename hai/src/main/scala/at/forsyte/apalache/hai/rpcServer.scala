package at.forsyte.apalache.hai.v1

import zio.{Ref, ZEnv}
import java.util.UUID
import scalapb.zio_grpc.ServerMain
import scalapb.zio_grpc.ServiceList

object RpcServer extends ServerMain {
  override def port: Int = 8822

  val createService = for {
    // A thread safe mutable reference to the active connections
    // See https://zio.dev/version-1.x/datatypes/concurrency/ref/
    connections <- Ref.make(Map[UUID, Conn]())
  } yield new TransExplorerService(connections)

  def services: ServiceList[ZEnv] =
    ServiceList.addM(createService)
}
