package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestBase
import org.scalatest.Tag

import java.nio.file.Files

/** Marks scenarios used by the array-encoding CI slice. */
object ArrayEncoding extends Tag("array-encoding")

/** Exercises representative CLI model-checking scenarios. */
class CheckCommandTest extends IntegrationTestBase {
  test("check factorization find a counterexample", ArrayEncoding) {
    run(
        "check",
        outDirArgument,
        "--tuning-options=cvc5.smt.logic=QF_UFNIA",
        "--length=2",
        "--inv=Inv",
        workspace.fixture("factorization.tla").toString,
    ).expectExit(12)
      .expectOutput("""
          |...
          |The outcome is: Error
          |Checker has found an error
          |...
          |EXITCODE: ERROR (12)
          |""".stripMargin)
  }

  test("check Fix531.tla reports no error: regression for issue 531", ArrayEncoding) {
    run("check", outDirArgument, "--length=1", workspace.fixture("Fix531.tla").toString)
      .expectSuccess()
      .expectOutput("""
          |...
          |The outcome is: NoError
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("configure via TLC config and override it via CLI") {
    run(
        "check",
        outDirArgument,
        s"--config=${workspace.fixture("Config1.cfg")}",
        "--init=Init2",
        "--next=Next2",
        workspace.fixture("Config.tla").toString,
    ).expectExit(12)
      .expectOutput("""
          |...
          |  > Config1.cfg: Loading TLC configuration
          |...
          |  > Set the initialization predicate to Init2
          |  > Set the transition predicate to Next2
          |  > Set an invariant to Inv1
          |...
          |State 7: state invariant 0 violated.
          |Found 1 error(s)
          |The outcome is: Error
          |Checker has found an error
          |...
          |EXITCODE: ERROR (12)
          |""".stripMargin)
  }

  test("output manager: write-intermediate files") {
    run(
        "check",
        outDirArgument,
        "--write-intermediate=true",
        "--length=0",
        workspace.fixture("Counter.tla").toString,
    ).expectSuccess()

    val passNames = Vector(
      "OutSanyParser",
      "OutTypeCheckerSnowcat",
      "OutConfigurationPass",
      "OutDesugarerPass",
      "OutInlinePass",
      "OutTemporalPass",
      "OutInlinePass",
      "OutPrimingPass",
      "OutVCGen",
      "OutPreprocessingPass",
      "OutTransitionFinderPass",
      "OutOptimizationPass",
      "OutAnalysisPass",
    )
    val expectedIntermediateFiles = (0 to 12).flatMap { index =>
      val base = f"$index%02d_${passNames(index)}"
      Seq(s"intermediate/$base.json", s"intermediate/$base.tla")
    }.toSet
    val expectedFiles = expectedIntermediateFiles ++ Set("detailed.log", "log0.smt", "run.txt")
    val runDirectory = workspace.singleRunDirectory("Counter.tla")

    assert(workspace.filesBelow(runDirectory) == expectedFiles)
  }

  test("quint input: bigints are deserialized correctly") {
    run(
        "check",
        outDirArgument,
        "--init=init",
        "--next=step",
        "--inv=inv",
        workspace.fixture("bigint.qnt.json").toString,
    ).expectExit(12)
      .expectOutput("""
          |...
          |EXITCODE: ERROR (12)
          |""".stripMargin)

    val violation = workspace.singleRunDirectory("bigint.qnt.json").resolve("violation.tla")
    assert(Files.isRegularFile(violation))
    assert(workspace.read(violation).contains("State0 == balance = 100000000000"))
  }
}
