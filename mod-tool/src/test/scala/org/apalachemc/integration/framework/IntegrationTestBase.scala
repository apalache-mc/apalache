package org.apalachemc.integration.framework

import org.scalatest.BeforeAndAfterEach
import org.scalatest.{Args, Outcome, Status, SucceededStatus}
import org.scalatest.funsuite.AnyFunSuite

/** Supplies each command suite with an isolated workspace and selected Tool runner. */
abstract class IntegrationTestBase extends AnyFunSuite with BeforeAndAfterEach {
  import IntegrationTestConfiguration.GENERAL

  private val reportTimings = sys.env.get("APALACHE_CLI_TEST_TIMING").exists(_.equalsIgnoreCase("true"))
  private var currentRunner: ToolRunner = _
  private var currentWorkspace: TestWorkspace = _

  /** Configurations under which this entire suite is valid. */
  protected def supportedConfigurations: Set[IntegrationTestConfiguration] = Set(GENERAL)

  /** Configuration selected for this worker process. */
  final protected def activeConfiguration: IntegrationTestConfiguration = IntegrationTestConfiguration.active

  /** Distinguishes reports emitted by parallel configuration workers. */
  final override def suiteName: String = s"${super.suiteName} [${activeConfiguration.id}]"

  /** Returns the isolated workspace belonging to the current test. */
  final protected def workspace: TestWorkspace = {
    require(currentWorkspace != null, "The test workspace is only available while a test is running")
    currentWorkspace
  }

  /** Runs Tool with the current test's execution mode and workspace. */
  final protected def run(arguments: String*): CommandResult = {
    require(currentRunner != null, "The Tool runner is only available while a test is running")
    val result = currentRunner.run(workspace, arguments)
    if (reportTimings) {
      println(
          f"CLI_TEST_COMMAND_TIME_MS configuration=${activeConfiguration.id} " +
            f"elapsed=${result.elapsed.toNanos / 1000000.0}%.3f")
    }
    result
  }

  /** Runs a command with its output directory set to the current workspace. */
  final protected def runWithOutDir(command: String, arguments: String*): CommandResult =
    run((Seq(command, s"--out-dir=${workspace.outDir}") ++ arguments): _*)

  /** Silently omits this suite from workers whose configuration it does not support. */
  override protected def runTests(testName: Option[String], args: Args): Status = {
    IntegrationTestConfiguration.validateSupported(supportedConfigurations)
    if (supportedConfigurations.contains(activeConfiguration)) {
      activeConfiguration.validateEnvironment(sys.env)
      super.runTests(testName, args)
    } else {
      SucceededStatus
    }
  }

  /** Selects the runner indicated by the current test's tags. */
  override protected def withFixture(test: NoArgTest): Outcome = {
    currentRunner = ToolRunner.selected(forceForked = test.tags.contains(Forked.name))
    try {
      super.withFixture(test)
    } finally {
      currentRunner = null
    }
  }

  /** Creates an isolated workspace before each test. */
  override protected def beforeEach(): Unit = {
    super.beforeEach()
    currentWorkspace = TestWorkspace.create()
  }

  /** Deletes the current test's workspace after execution. */
  override protected def afterEach(): Unit = {
    try {
      if (currentWorkspace != null) {
        currentWorkspace.close()
      }
    } finally {
      currentWorkspace = null
      super.afterEach()
    }
  }
}
