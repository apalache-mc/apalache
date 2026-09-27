package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestConfiguration.{ARRAYS_Z3, OOPSLA19_CVC5, OOPSLA19_Z3}
import org.apalachemc.integration.framework.{IntegrationTestBase, IntegrationTestConfiguration}

/** Shared support for suites that exercise the check command. */
private[integration] abstract class CheckCommandTestBase extends IntegrationTestBase {
  final protected def check(arguments: String*) = runWithOutDir("check", arguments: _*)
}

/** Exercises checks that work with every solver/encoding pair in the integration-test matrix. */
class CheckCommandTest extends CheckCommandTestBase {
  override protected val supportedConfigurations: Set[IntegrationTestConfiguration] =
    Set(OOPSLA19_Z3, OOPSLA19_CVC5, ARRAYS_Z3)

  test("check factorization find a counterexample") {
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

  test("check Fix531.tla reports no error: regression for issue 531") {
    check("--length=1", workspace.filename("Fix531.tla"))
      .expectSuccess()
      .expectOutput("""
          |...
          |The outcome is: NoError
          |...
          |EXITCODE: OK
          |""".stripMargin)
  }

  test("check UnchangedExpr471.tla reports no error: regression for issue 471") {
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

  test("check Bug593 fails correctly: regression for issue 593") {
    check(workspace.filename("Bug593.tla"))
      .expectExit(255)
      .expectOutput("""
          |...
          |EXITCODE: ERROR (255)
          |""".stripMargin)
  }

  test("check HandshakeWithTypes.tla with length 5 deadlocks") {
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
}
