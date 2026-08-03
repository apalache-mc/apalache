package org.apalachemc.integration

import org.apalachemc.integration.framework.{Forked, IntegrationTestBase}
import org.scalatest.Tag

import java.nio.file.Files

/** Marks scenarios used by the array-encoding CI slice. */
object ArrayEncoding extends Tag("array-encoding")

/** Marks scenarios that exercise temporal model checking. */
object Temporal extends Tag("temporal")

/** Exercises representative CLI model-checking scenarios. */
class CheckCommandTest extends IntegrationTestBase {
  private def check(arguments: String*) = runWithOutDir("check", arguments: _*)

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

  test("check factorization find a counterexample", ArrayEncoding) {
    check(
        "--tuning-options=cvc5.smt.logic=QF_UFNIA",
        "--length=2",
        "--inv=Inv",
        workspace.filename("factorization.tla"),
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
    check("--length=1", workspace.filename("Fix531.tla"))
      .expectSuccess()
      .expectOutput("""
          |...
          |The outcome is: NoError
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("check UnchangedExpr471.tla reports no error: regression for issue 471", ArrayEncoding) {
    check(
        "--cinit=ConstInit",
        "--length=1",
        workspace.filename("UnchangedExpr471.tla"),
    ).expectSuccess()
      .expectOutput("""
          |...
          |The outcome is: NoError
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("check Bug593 fails correctly: regression for issue 593", ArrayEncoding) {
    check(workspace.filename("Bug593.tla"))
      .expectExit(255)
      .expectOutput("""
          |...
          |EXITCODE: ERROR (255)
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

  test("check HandshakeWithTypes.tla with length 5 deadlocks", ArrayEncoding) {
    check(
        "--length=5",
        "--inv=Inv",
        workspace.filename("HandshakeWithTypes.tla"),
    ).expectExit(12)
      .expectOutput("""
          |...
          |The outcome is: Deadlock
          |...
          |EXITCODE: ERROR (12)
          |""".stripMargin)
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

  test("check NonLinearArithmetic.tla with default CVC5 logic reports how to enable nonlinear arithmetic") {
    check(
        "--smt-solver=cvc5",
        "--length=0",
        "--inv=SquareNonNegative",
        workspace.filename("NonLinearArithmetic.tla"),
    ).expectExit(255)
      .expectContains(
          "cvc5 is using SMT logic QF_UFLIA, which only permits linear integer arithmetic, but the solver saw a nonlinear arithmetic term")
      .expectContains("Re-run with --tuning-options=cvc5.smt.logic=QF_UFNIA.")
      .expectContains("EXITCODE: ERROR (255)")
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
