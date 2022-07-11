package at.forsyte.apalache.shai.v1

import zio._
import zio.test._
import zio.test.Assertion._
import at.forsyte.apalache.shai.v1.transExplorer.{ConnectRequest, LoadModelRequest}

object TransExplorerServiceSpec extends DefaultRunnableSpec {

  // Basic service for use in tests
  // val service: UIO[TransExplorerService] = RpcServer.createService

  def spec = suite("TransExplorerServiceSpec")(
      testM("can obtain two different connections to server") {
        for {
          s <- ZIO.service[TransExplorerService]
          c1 <- s.openConnection(ConnectRequest())
          c2 <- s.openConnection(ConnectRequest())
        } yield assert(c1.id)(not(equalTo(c2.id)))
      },
      testM("invalid spec returns error") {
        val spec = """|---- missing module declaration ----
                      |Foo == TRUE
                      |====
                      |""".stripMargin
        for {
          s <- ZIO.service[TransExplorerService]
          conn <- s.openConnection(ConnectRequest())
          resp <- s.loadModel(LoadModelRequest(conn.id, spec))
          msg = resp.result.err.get
        } yield assert(msg)(containsString("Parsing failed: Error by TLA+ parser"))
      },
      testM("valid spec returns parsed model") {
        val spec =
          """|---- MODULE A ----
             |Foo == TRUE
             |====
             |""".stripMargin

        for {
          s <- ZIO.service[TransExplorerService]
          conn <- s.openConnection(ConnectRequest())
          resp <- s.loadModel(LoadModelRequest(conn.id, spec))
        } yield assert(resp.result.isSpec)(isTrue)
      },
      testM("valid multi-module spec loads parsed model") {
        val auxSpec =
          """|---- MODULE B ----
             |BOp == TRUE
             |==================
             |""".stripMargin

        val spec =
          """|---- MODULE A ----
             |EXTENDS B
             |Foo == BOp
             |==================
             |""".stripMargin
        for {
          s <- ZIO.service[TransExplorerService]
          conn <- s.openConnection(ConnectRequest())
          resp <- s.loadModel(LoadModelRequest(conn.id, spec, Seq(auxSpec)))
        } yield assert(resp.result.isSpec)(isTrue)
      },
  )
    // Create the single shared service for use in our tests, allowing us to run
    // all tests as if they were against the same service this accurately
    // reflects our usage, since only one server instance will ever be running
    // in an Apalache process at a time
    .provideSomeLayerShared[ZEnv](RpcServer.createService.toLayer)
}
