package at.forsyte.apalache.shai.v1

import zio._
import zio.test._
import zio.test.Assertion._
import java.util.UUID
import at.forsyte.apalache.shai.v1.transExplorer.ConnectRequest

object TransExplorerServiceSpec extends DefaultRunnableSpec {

  // Basic service for use in tests
  val service: UIO[TransExplorerService] = for {
    connections <- Ref.make(Map[UUID, Conn]())
  } yield new TransExplorerService(connections)

  def spec = suite("TransExplorerServiceSpec")(
      testM("can obtain two different connections to server") {
        for {
          s <- service
          c1 <- s.openConnection(ConnectRequest())
          c2 <- s.openConnection(ConnectRequest())
        } yield assert(c1.id)(not(equalTo(c2.id)))
      }
  )
}
