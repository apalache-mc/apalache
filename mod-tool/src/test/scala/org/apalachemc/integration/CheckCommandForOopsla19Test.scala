package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestConfiguration.{OOPSLA19_CVC5, OOPSLA19_Z3}
import org.apalachemc.integration.framework.{Forked, IntegrationTestConfiguration}
import org.scalatest.Tag

import java.nio.file.Files

/** Marks scenarios that exercise temporal model checking. */
object Temporal extends Tag("temporal")

/** Exercises check-command behavior that is supported by OOPSLA19 but not by the arrays encoding. */
class CheckCommandForOopsla19Test extends CheckCommandTestBase {
  override protected val supportedConfigurations: Set[IntegrationTestConfiguration] =
    Set(OOPSLA19_Z3, OOPSLA19_CVC5)

  test("check command emits no Java 25 compatibility warnings", Forked) {
    val result = check("--length=1", workspace.filename("NoVars.tla"))
      .expectSuccess()

    Seq(result.stdout, result.stderr).foreach { output =>
      val lowerCaseOutput = output.toLowerCase
      assert(!lowerCaseOutput.contains("terminally deprecated"))
      assert(!lowerCaseOutput.contains("restricted method"))
    }
  }

  test("Prints default computation length of 10 (regression #2087)") {
    check(workspace.filename("y2k_instance.tla"))
      .expectSuccess()
      .expectOutput("""
          |...
          |The outcome is: NoError
          |Checker reports no error up to computation length 10
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("check Bug3400 reports SANY semantic error") {
    val result = check(
        "--init=IndInv1",
        "--next=Next",
        "--inv=IndInv1",
        workspace.filename("Bug3400.tla"),
    ).expectExit(255)

    result
      .expectContains("Parsing error: Semantic errors:")
      .expectContains("line 14, col 12 to line 14, col 18 of module Bug3400")
      .expectContains("Unknown operator: `IndInv1'.")
      .expectContains("EXITCODE: ERROR (255)")
      .expectNotContains("Unknown SANY error")
  }

  test("check HandshakeWithTypes.tla with length 5 passes with --no-deadlock") {
    check(
        "--length=5",
        "--no-deadlock=1",
        "--inv=Inv",
        workspace.filename("HandshakeWithTypes.tla"),
    ).expectSuccess()
      .expectOutput("""
          |...
          |The outcome is: ExecutionsTooShort
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("check Rec1.tla fails check") {
    check(
        "--length=5",
        "--inv=Inv",
        workspace.filename("Rec1.tla"),
    ).expectExit(255)
      .expectOutput("""
          |...
          |EXITCODE: ERROR (255)
          |""".stripMargin)
  }

  test("check FalseLiveness fails", Temporal) {
    check(
        "--temporal=FalseLiveness",
        workspace.filename("LongPrefix.tla"),
    ).expectExit(12)
      .expectOutput("""
          |...
          |EXITCODE: ERROR (12)
          |""".stripMargin)
  }

  test("configure via TLC config and override it via CLI") {
    check(
        s"--config=${workspace.filename("Config1.cfg")}",
        "--init=Init2",
        "--next=Next2",
        workspace.filename("Config.tla"),
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
    check(
        "--write-intermediate=true",
        "--length=0",
        workspace.filename("Counter.tla"),
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
    check(
        "--init=init",
        "--next=step",
        "--inv=inv",
        workspace.filename("bigint.qnt.json"),
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
