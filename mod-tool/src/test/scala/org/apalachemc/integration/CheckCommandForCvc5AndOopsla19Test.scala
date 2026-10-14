package org.apalachemc.integration

import org.apalachemc.integration.framework.IntegrationTestConfiguration.OOPSLA19_CVC5
import org.apalachemc.integration.framework.IntegrationTestConfiguration

/** Exercises check-command behavior specific to CVC5 with the OOPSLA19 encoding. */
class CheckCommandForCvc5AndOopsla19Test extends CheckCommandTestBase {
  override protected val supportedConfigurations: Set[IntegrationTestConfiguration] = Set(OOPSLA19_CVC5)

  test("check NonLinearArithmetic.tla with default CVC5 logic reports how to enable nonlinear arithmetic") {
    check(
        "--length=0",
        "--inv=SquareNonNegative",
        workspace.filename("NonLinearArithmetic.tla"),
    ).expectExit(255)
      .expectContains(
          "cvc5 is using SMT logic QF_UFLIA, which only permits linear integer arithmetic, but the solver saw a nonlinear arithmetic term")
      .expectContains("Re-run with --tuning-options=cvc5.smt.logic=QF_UFNIA.")
      .expectContains("EXITCODE: ERROR (255)")
  }
}
