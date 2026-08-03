package org.apalachemc.integration

import org.apalachemc.integration.framework.{CommandResult, Forked, OutputMatcher, TestWorkspace, ToolMode, ToolRunner}
import org.scalatest.funsuite.AnyFunSuite

import scala.concurrent.duration.Duration

/** Verifies the reusable CLI integration-test support. */
class IntegrationSupportTest extends AnyFunSuite {
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
      assert(workspace.fixture("Empty.tla").getFileName.toString == "Empty.tla")
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

  test("workspace finds repository fixtures when the root property is absent") {
    val property = "apalache.cli.test.repo-root"
    val previousRoot = Option(System.getProperty(property))
    try {
      System.clearProperty(property)
      val workspace = TestWorkspace.create()
      try {
        assert(workspace.fixture("factorization.tla").getFileName.toString == "factorization.tla")
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
