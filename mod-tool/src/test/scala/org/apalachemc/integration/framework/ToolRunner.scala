package org.apalachemc.integration.framework

import at.forsyte.apalache.tla.Tool
import ch.qos.logback.classic.LoggerContext
import org.slf4j.LoggerFactory

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.Paths
import java.util.concurrent.TimeUnit
import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, Future, blocking}
import scala.jdk.CollectionConverters._

/** Identifies how an integration scenario invokes Tool. */
sealed trait ToolMode

/** Parses the configured Tool execution mode. */
object ToolMode {
  case object InProcess extends ToolMode
  case object Forked extends ToolMode

  /** Parses an optional execution-mode setting, defaulting to in-process. */
  def parse(value: Option[String]): ToolMode = value.map(_.trim.toLowerCase) match {
    case None | Some("") | Some("in-process") => InProcess
    case Some("forked")                        => Forked
    case Some(other) =>
      throw new IllegalArgumentException(
          s"Unknown APALACHE_CLI_TEST_MODE '$other'; expected 'in-process' or 'forked'")
  }
}

/** Executes Tool arguments in an isolated test workspace. */
trait ToolRunner {
  /** Runs Tool and captures its exit code, output streams, and elapsed time. */
  def run(workspace: TestWorkspace, arguments: Seq[String]): CommandResult
}

/** Selects a Tool runner from the integration-test environment. */
object ToolRunner {
  private val ModeEnvironmentVariable = "APALACHE_CLI_TEST_MODE"

  /** Selects the configured runner unless the current test requires forking. */
  def selected(forceForked: Boolean = false): ToolRunner =
    effectiveMode(ToolMode.parse(Option(System.getenv(ModeEnvironmentVariable))), forceForked) match {
    case ToolMode.InProcess => InProcessToolRunner
    case ToolMode.Forked    => ForkedToolRunner
  }

  /** Resolves a configured mode and a per-test forking requirement. */
  private[integration] def effectiveMode(configuredMode: ToolMode, forceForked: Boolean): ToolMode =
    if (forceForked) ToolMode.Forked else configuredMode
}

/** Reuses the integration-test JVM while capturing global streams safely. */
private object InProcessToolRunner extends ToolRunner {
  private val lock = new Object

  /** Runs Tool in this JVM while serializing access to process-global state. */
  override def run(workspace: TestWorkspace, arguments: Seq[String]): CommandResult = lock.synchronized {
    val stdout = new ByteArrayOutputStream()
    val stderr = new ByteArrayOutputStream()
    val out = new PrintStream(stdout, true, StandardCharsets.UTF_8)
    val err = new PrintStream(stderr, true, StandardCharsets.UTF_8)
    val previousOut = System.out
    val previousErr = System.err
    val previousHome = Option(System.getProperty("user.home"))
    val previousTemporaryDirectory = Option(System.getProperty("java.io.tmpdir"))
    val startedAt = System.nanoTime()

    try {
      System.setOut(out)
      System.setErr(err)
      System.setProperty("user.home", workspace.home.toString)
      System.setProperty("java.io.tmpdir", workspace.temporaryDirectory.toString)
      val exitCode = scala.Console.withOut(out) {
        scala.Console.withErr(err) {
          Tool.run(arguments.toArray, isReset = true, isConsoleDecorated = false)
        }
      }
      val elapsed = (System.nanoTime() - startedAt).nanos
      out.flush()
      err.flush()
      CommandResult(
          arguments,
          exitCode,
          stdout.toString(StandardCharsets.UTF_8),
          stderr.toString(StandardCharsets.UTF_8),
          elapsed,
      )
    } finally {
      LoggerFactory.getILoggerFactory.asInstanceOf[LoggerContext].reset()
      System.setOut(previousOut)
      System.setErr(previousErr)
      restoreProperty("user.home", previousHome)
      restoreProperty("java.io.tmpdir", previousTemporaryDirectory)
      out.close()
      err.close()
    }
  }

  private def restoreProperty(name: String, value: Option[String]): Unit = value match {
    case Some(previous) => System.setProperty(name, previous)
    case None           => System.clearProperty(name)
  }

}

/** Starts a fresh JVM for every Tool invocation. */
private object ForkedToolRunner extends ToolRunner {
  private val ClasspathProperty = "apalache.cli.test.classpath"
  private val Timeout = 5.minutes

  /** Runs Tool in a child JVM and captures its two output streams separately. */
  override def run(workspace: TestWorkspace, arguments: Seq[String]): CommandResult = {
    val command = Seq(javaExecutable) ++ compatibilityArguments ++ Seq(
        s"-Duser.home=${workspace.home}",
        s"-Djava.io.tmpdir=${workspace.temporaryDirectory}",
        "-cp",
        toolClasspath,
        "org.apalachemc.integration.framework.ForkedToolMain",
    ) ++ arguments
    val process = new ProcessBuilder(command.asJava)
      .directory(workspace.root.toFile)
      .start()
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    val stdout = Future(blocking(new String(process.getInputStream.readAllBytes(), StandardCharsets.UTF_8)))
    val stderr = Future(blocking(new String(process.getErrorStream.readAllBytes(), StandardCharsets.UTF_8)))
    val startedAt = System.nanoTime()
    val completed = process.waitFor(Timeout.toMillis, TimeUnit.MILLISECONDS)

    if (!completed) {
      process.destroyForcibly()
      throw new IllegalStateException(s"Forked Tool timed out after $Timeout: ${arguments.mkString(" ")}")
    }

    val elapsed = (System.nanoTime() - startedAt).nanos
    val capturedStdout = Await.result(stdout, 10.seconds)
    val capturedStderr = Await.result(stderr, 10.seconds)
    CommandResult(
        arguments,
        process.exitValue(),
        capturedStdout,
        capturedStderr,
        elapsed,
    )
  }

  private def javaExecutable: String = {
    val executable = if (System.getProperty("os.name").toLowerCase.contains("win")) "java.exe" else "java"
    Paths.get(System.getProperty("java.home"), "bin", executable).toString
  }

  private def compatibilityArguments: Seq[String] = {
    val javaFeature = Runtime.version().feature()
    (if (javaFeature >= 22) Seq("--enable-native-access=ALL-UNNAMED") else Seq.empty) ++
      (if (javaFeature >= 24) Seq("--sun-misc-unsafe-memory-access=allow") else Seq.empty)
  }

  private def toolClasspath: String =
    Option(System.getProperty(ClasspathProperty))
      .orElse(Option(System.getProperty("java.class.path")))
      .filter(_.nonEmpty)
      .getOrElse(throw new IllegalStateException("The Tool classpath is unavailable"))
}
