package org.apalachemc.integration

import at.forsyte.apalache.io.config.{SMTEncoding, SMTSolver}
import org.apalachemc.integration.framework.IntegrationTestConfiguration.{ARRAYS_Z3, GENERAL, OOPSLA19_CVC5, OOPSLA19_Z3}
import org.apalachemc.integration.framework.{CommandResult, Forked, IntegrationTestBase, IntegrationTestConfiguration,
  OutputMatcher, TestWorkspace, ToolMode, ToolRunner}

import scala.concurrent.duration.Duration

/** Verifies the reusable CLI integration-test support. */
class IntegrationSupportTest extends IntegrationTestBase {
  test("integration-test configurations have stable IDs and environment mappings") {
    assert(IntegrationTestConfiguration.parse("general") == GENERAL)
    assert(IntegrationTestConfiguration.parse("oopsla19-z3") == OOPSLA19_Z3)
    assert(IntegrationTestConfiguration.parse("oopsla19-cvc5") == OOPSLA19_CVC5)
    assert(IntegrationTestConfiguration.parse("arrays-z3") == ARRAYS_Z3)

    assert(OOPSLA19_Z3.solver == SMTSolver.Z3)
    assert(OOPSLA19_Z3.encoding == SMTEncoding.OOPSLA19)
    assert(OOPSLA19_Z3.environment == Map("SMT_SOLVER" -> "z3", "SMT_ENCODING" -> "oopsla19"))
    assert(OOPSLA19_CVC5.environment == Map("SMT_SOLVER" -> "cvc5", "SMT_ENCODING" -> "oopsla19"))
    assert(ARRAYS_Z3.environment == Map("SMT_SOLVER" -> "z3", "SMT_ENCODING" -> "arrays"))
  }

  test("integration-test configurations reject unknown IDs and empty supported sets") {
    val unknown = intercept[IllegalArgumentException] {
      IntegrationTestConfiguration.parse("arrays-cvc5")
    }
    assert(unknown.getMessage.contains("Unknown integration-test configuration 'arrays-cvc5'"))

    val empty = intercept[IllegalArgumentException] {
      IntegrationTestConfiguration.validateSupported(Set.empty)
    }
    assert(empty.getMessage.contains("must support at least one configuration"))
  }

  test("checker configurations validate their worker environment") {
    OOPSLA19_Z3.validateEnvironment(Map("SMT_SOLVER" -> "z3", "SMT_ENCODING" -> "oopsla19"))

    val mismatch = intercept[IllegalArgumentException] {
      OOPSLA19_Z3.validateEnvironment(Map("SMT_SOLVER" -> "cvc5", "SMT_ENCODING" -> "oopsla19"))
    }
    assert(mismatch.getMessage.contains("expected SMT_SOLVER=z3, but got cvc5"))
  }

  test("output normalization handles line endings and trailing whitespace") {
    val actual = "first line  \r\nsecond line   \r\n"
    assert(OutputMatcher.normalize(actual) == "first line\nsecond line")
  }

  test("whole-line ellipses match zero or more output lines") {
    val expected = """
        |first
        |...
        |last
        |""".stripMargin
    assert(OutputMatcher.matches(expected, "first\nlast\n"))
    assert(OutputMatcher.matches(expected, "first\nmiddle one\nmiddle two\nlast\n"))
    assert(!OutputMatcher.matches(expected, "prefix\nfirst\nlast\n"))
  }

  test("leading and trailing ellipses allow surrounding output") {
    val expected = """
        |...
        |important
        |...
        |""".stripMargin
    assert(OutputMatcher.matches(expected, "before\nimportant\nafter"))
  }

  test("workspace creates isolated statistics and output directories") {
    val workspace = TestWorkspace.create()
    try {
      assert(workspace.read(workspace.home.resolve(".tlaplus").resolve("esc.txt")) == "NO_STATISTICS\n")
      assert(workspace.outDir.startsWith(workspace.root))
      assert(workspace.path("Empty.tla").getFileName.toString == "Empty.tla")
    } finally {
      workspace.close()
    }
  }

  test("workspace uses its temporary root when no repository root is configured") {
    val workspace = TestWorkspace.create(configuredRepoRoot = None)
    try {
      assert(workspace.repoRoot == workspace.root)
    } finally {
      workspace.close()
    }
  }

  test("workspace finds repository input files when the root property is absent") {
    val property = "apalache.cli.test.repo-root"
    val previousRoot = Option(System.getProperty(property))
    try {
      System.clearProperty(property)
      val workspace = TestWorkspace.create()
      try {
        assert(workspace.path("factorization.tla").getFileName.toString == "factorization.tla")
      } finally {
        workspace.close()
      }
    } finally {
      previousRoot match {
        case Some(root) => System.setProperty(property, root)
        case None       => System.clearProperty(property)
      }
    }
  }

  test("unknown execution modes are rejected") {
    val error = intercept[IllegalArgumentException](ToolMode.parse(Some("container")))
    assert(error.getMessage.contains("expected 'in-process' or 'forked'"))
  }

  test("Forked tag overrides the configured in-process mode") {
    assert(ToolRunner.effectiveMode(ToolMode.InProcess, forceForked = false) == ToolMode.InProcess)
    assert(ToolRunner.effectiveMode(ToolMode.InProcess, forceForked = true) == ToolMode.Forked)
    assert(Forked.name == "org.apalachemc.integration.framework.Forked")
  }

  test("command assertions select stdout or stderr without mixing them") {
    val result = CommandResult(
        Seq("test"),
        exitCode = 0,
        stdout = "stdout marker\n",
        stderr = "stderr marker\n",
        elapsed = Duration.Zero,
    )

    result
      .expectContains("stdout marker")
      .expectNotContains("stderr marker")
      .expectOutput("stdout marker")
      .expectContains("stderr marker", isStderr = true)
      .expectNotContains("stdout marker", isStderr = true)
      .expectOutput("stderr marker", isStderr = true)
  }
}
