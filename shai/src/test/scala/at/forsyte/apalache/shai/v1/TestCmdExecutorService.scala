package at.forsyte.apalache.shai.v1

import zio._
import zio.test._
import zio.test.Assertion._

import at.forsyte.apalache.shai.v1.cmdExecutor.{Cmd, CmdRequest}
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.io.ConfigManager

// Defines the test cases used to test the CmdExecutor service
object TestCmdExecutorService extends DefaultRunnableSpec {
  private val trivialSpec =
    """|---- MODULE M ----
       |Foo == TRUE
       |====
       |""".stripMargin

  def parseCmd(
      content: String,
      aux: Seq[String] = Seq(),
      cfg: Config.ApalacheConfig = Config.ApalacheConfig()): CmdRequest = {
    val config = {
      import Config._
      import SourceOption._
      val updatedCfg =
        cfg.copy(input = Input(source = Some(StringSource(content = content, aux = aux, format = Format.Tla))))
      ConfigManager.serialize(updatedCfg)
    }

    CmdRequest(cmd = Cmd.PARSE, config = config)
  }

  val spec = suite("CmdExecutorServiceSpec")(
      testM("can load module using the parse cmd") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(parseCmd(trivialSpec))
        } yield assert(resp.result.isSuccess)(isTrue)
      },
      testM("parsing invalid module input returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(parseCmd("INVALID SPEC"))
        } yield assert(resp.result.failure.get)(containsString("No module name found"))
      },
      testM("rpc with invalid config returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          config = ConfigManager.serialize(Config.ApalacheConfig())
          resp <- s.run(CmdRequest(cmd = Cmd.PARSE, config = config))
        } yield assert(resp.result.failure.get)(containsString("Missing value for required option input.source"))
      },
  ).provideSomeLayerShared[ZEnv](RpcServer.createCmdExecutorService.toLayer)
}
