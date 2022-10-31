package at.forsyte.apalache.shai.v1

import zio._
import zio.test._
import zio.test.Assertion._
import at.forsyte.apalache.shai.v1.transExplorer.{ConnectRequest, LoadModelRequest, PingRequest, PongResponse}

object TransExplorerServiceSpec extends DefaultRunnableSpec {

  def spec = suite("TransExplorerServiceSpec")(
      testM("can ping service") {
        for {
          s <- ZIO.service[TransExplorerService]
          resp <- s.ping(PingRequest())
        } yield assert(resp.isInstanceOf[PongResponse])(isTrue)
      },
      testM("can obtain two different connections to server") {
        for {
          s <- ZIO.service[TransExplorerService]
          c1 <- s.openConnection(ConnectRequest())
          c2 <- s.openConnection(ConnectRequest())
        } yield assert(c1.id)(not(equalTo(c2.id)))
      },
      testM("invalid spec returns error") {
        val spec =
          """|---- missing module declaration ----
             |Foo == TRUE
             |====
             |""".stripMargin
        for {
          s <- ZIO.service[TransExplorerService]
          conn <- s.openConnection(ConnectRequest())
          resp <- s.loadModel(LoadModelRequest(Some(conn), spec))
          msg = ujson.read(resp.result.err.get.data)("error_data")(0).str
        } yield assert(msg)(containsString("No module name found in source"))
      },
      testM("loading a valid spec returns parsed model") {
        val spec =
          """|---- MODULE D ----
             |Foo == TRUE
             |====
             |""".stripMargin

        for {
          s <- ZIO.service[TransExplorerService]
          conn <- s.openConnection(ConnectRequest())
          resp <- s.loadModel(LoadModelRequest(Some(conn), spec))
        } yield assert(resp.result.isSpec)(isTrue)
      },
      testM("valid multi-module spec loads into a parsed model") {
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
          resp <- s.loadModel(LoadModelRequest(Some(conn), spec, Seq(auxSpec)))
        } yield assert(resp.result.isSpec)(isTrue)
      },
      testM("can load two valid specs in sequence") {
        val specA =
          """|---- MODULE A ----
             |Foo == TRUE
             |====
             |""".stripMargin

        val specB =
          """|---- MODULE B ----
             |Foo == TRUE
             |====
             |""".stripMargin

        for {
          s <- ZIO.service[TransExplorerService]
          conn <- s.openConnection(ConnectRequest())
          respA <- s.loadModel(LoadModelRequest(Some(conn), specA))
          respB <- s.loadModel(LoadModelRequest(Some(conn), specB))
        } yield assert(respA.result.isSpec && respB.result.isSpec)(isTrue)
      },
      testM("can load two valid specs in parallel") {
        val specA =
          """|---- MODULE A ----
             |Foo == TRUE
             |====
             |""".stripMargin

        val specB =
          """|---- MODULE B ----
             |Foo == TRUE
             |====
             |""".stripMargin

        for {
          s <- ZIO.service[TransExplorerService]
          // Run with two separate connections, because loading two specs in
          // parallel on the same connection isn't a feasible use case
          connA <- s.openConnection(ConnectRequest())
          connB <- s.openConnection(ConnectRequest())
          reqA = LoadModelRequest(Some(connA), specA)
          reqB = LoadModelRequest(Some(connB), specB)
          responses <- s.loadModel(reqA).zipPar(s.loadModel(reqB))
          (respA, respB) = responses
        } yield assert(respA.result.isSpec && respB.result.isSpec)(isTrue)
      },
  )
    // Create the single shared service for use in our tests, allowing us to run
    // all tests as if they were against the same service this accurately
    // reflects our usage, since only one server instance will ever be running
    // in an Apalache process at a time
    .provideSomeLayerShared[ZEnv](RpcServer().createTransExplorerService.toLayer)
}
