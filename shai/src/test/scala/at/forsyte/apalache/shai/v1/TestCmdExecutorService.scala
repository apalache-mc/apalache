package at.forsyte.apalache.shai.v1

import at.forsyte.apalache.io.InputSource
import at.forsyte.apalache.io.config.{ApalacheConfig, ApalacheConfigJsonParser, CheckerPatch}
import at.forsyte.apalache.shai.v1.cmdExecutor._
import io.grpc.Status
import zio._
import zio.test.Assertion._
import zio.test._

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
      cfg: ApalacheConfig = ApalacheConfig.empty): CmdRequest = {
    val source = InputSource.StringSource(content = content, aux = aux.toList, format = InputSource.Format.Tla)
    val config = ApalacheConfigJsonParser.write(cfg.copy(source = Some(source)))

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
          msg = resp.result.failure.get.data
        } yield assert(msg)(containsString("No module name found"))
      },
      testM("rpc with invalid config returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          config = ApalacheConfigJsonParser.write(ApalacheConfig.empty)
          resp <- s.run(CmdRequest(cmd = Cmd.PARSE, config = config))
          msg = resp.result.failure.get.data
        } yield assert(msg)(containsString("Missing value for required option source"))
      },
      testM("rpc rejects file-backed input as an invalid argument") {
        for {
          s <- ZIO.service[CmdExecutorService]
          result <- s.run(CmdRequest(cmd = Cmd.PARSE, config = """{"source":"does-not-exist.tla"}""")).either
        } yield result match {
          case Left(status) =>
            assert(status.getCode)(equalTo(Status.Code.INVALID_ARGUMENT)) &&
            assert(status.getDescription)(containsString("$.source"))
          case Right(_) =>
            assert(false)(isTrue)
        }
      },
      testM("running check an invalid spec returns an error") {
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.CHECK, trivialSpec))
          msg = resp.result.failure.get.data
        } yield assert(msg)(containsString("Operator Init not found"))
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
          config = ApalacheConfig(checker = CheckerPatch(invariants = Some(List("Inv"))))
          resp <- s.run(runCmd(Cmd.CHECK, checkableSpec, cfg = config))
          err = resp.result.failure.get
          data = ujson.read(err.data)
        } yield {
          assert(err.errorType)(equalTo(CmdErrorType.PASS_FAILURE))
          assert(data("pass_name").str)(equalTo("BoundedChecker"))
          assert(data("error_data")("checking_result").str)(equalTo("violation"))
          assert(data("error_data")("counterexamples").arr)(isNonEmpty)
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
          err = resp.result.failure.get
          data = ujson.read(err.data)
        } yield {
          assert(err.errorType)(equalTo(CmdErrorType.PASS_FAILURE))
          assert(data("pass_name").str)(equalTo("TypeCheckerSnowcat"))
          assert(data("error_data").arr)(isNonEmpty)
        }
      },
      testM("can use TLA command to receive formatted TLA") {
        val expectedPayload =
          """|----------------------------------- MODULE M -----------------------------------
             |
             |EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants
             |
             |Foo == TRUE
             |
             |================================================================================
             |""".stripMargin
        for {
          s <- ZIO.service[CmdExecutorService]
          resp <- s.run(runCmd(Cmd.TLA, trivialSpec))
          actualPayload = ujson.read(resp.result.success.get).str
        } yield assert(actualPayload)(equalTo(expectedPayload))
      },
  )
    // Create the single shared service for use in our tests, allowing us to run
    // all tests as if they were against the same service this accurately
    // reflects our usage, since only one server instance will ever be running
    // in an Apalache process at a time
    .provideSomeLayerShared[ZEnv](RpcServer().createCmdExecutorService.toLayer)
}
