package at.forsyte.apalache.shai.v1

import zio._
import zio.test._
import zio.test.Assertion._

import at.forsyte.apalache.shai.v1.cmdExecutor.{Cmd, CmdRequest}
import at.forsyte.apalache.infra.passes.options.Config
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.io.ConfigManager
import at.forsyte.apalache.shai.v1.common.PingRequest
import at.forsyte.apalache.shai.v1.common.PongResponse

// Defines the test cases used to test the CmdExecutor service
object TestCmdExecutorService extends DefaultRunnableSpec {
  private val trivialSpec =
    """|---- MODULE M ----
       |Foo == TRUE
       |====
       |""".stripMargin

  private val checkableSpec =
    """|---- MODULE M ----
       |Init == TRUE
       |Next == TRUE
       |Inv == FALSE
       |====
       |""".stripMargin

  private val illTypedSpec =
    """|---- MODULE M ----
       |\* @type: () => Int;
       |Foo == TRUE
       |====
       |""".stripMargin

  def runCmd(
      cmd: Cmd,
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

    CmdRequest(cmd = cmd, config = config)
  }

  val spec = suite("CmdExecutorServiceSpec")(
      testM("can ping service") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.ping(PingRequest())
        } yield assert(resp.isInstanceOf[PongResponse])(isTrue)
      },
      testM("can load module using the parse cmd") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.PARSE, trivialSpec))
        } yield assert(resp.result.isSuccess)(isTrue)
      },
      testM("parsing invalid module input returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.PARSE, "INVALID SPEC"))
        } yield assert(resp.result.failure.get)(containsString("No module name found"))
      },
      testM("rpc with invalid config returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          config = ConfigManager.serialize(Config.ApalacheConfig())
          resp <- s.run(CmdRequest(cmd = Cmd.PARSE, config = config))
        } yield assert(resp.result.failure.get)(containsString("Missing value for required option input.source"))
      },
      testM("running check an invalid spec returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.CHECK, trivialSpec))
        } yield assert(resp.result.failure.get)(containsString("Operator Init not found"))
      },
      testM("running check on valid spec succeeds") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.CHECK, checkableSpec))
        } yield assert(resp.result.isSuccess)(isTrue)
      },
      testM("running check on spec with violated invariant fails") {
        for {
          s <- ZIO.service[CmdExecutorService]
          config = Config.ApalacheConfig(checker = Config.Checker(inv = Some(List("Inv"))))
          resp <- s.run(runCmd(Cmd.CHECK, checkableSpec, cfg = config))
          json = ujson.read(resp.result.failure.get)
        } yield {
          assert(json("error_type").str)(equalTo("pass_failure"))
          assert(json("data")("pass_name").str)(equalTo("BoundedChecker"))
          assert(json("data")("error_data")("checking_result").str)(equalTo("violation"))
          assert(json("data")("error_data")("counterexamples").arr)(isNonEmpty)
        }
      },
      testM("typechecking well-typed spec succeeds") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.TYPECHECK, trivialSpec))
        } yield assert(resp.result.isSuccess)(isTrue)
      },
      testM("typechecking ill-typed spec returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.TYPECHECK, illTypedSpec))
          json = ujson.read(resp.result.failure.get)
        } yield {
          assert(json("error_type").str)(equalTo("pass_failure"))
          assert(json("data")("pass_name").str)(equalTo("TypeCheckerSnowcat"))
          assert(json("data")("error_data").arr)(isNonEmpty)
        }
      },
  )
    // Create the single shared service for use in our tests, allowing us to run
    // all tests as if they were against the same service this accurately
    // reflects our usage, since only one server instance will ever be running
    // in an Apalache process at a time
    .provideSomeLayerShared[ZEnv](RpcServer.createCmdExecutorService.toLayer)
}
