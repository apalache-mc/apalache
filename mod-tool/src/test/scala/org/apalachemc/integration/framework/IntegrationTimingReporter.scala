package org.apalachemc.integration.framework

import java.io.{BufferedWriter, IOException}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths, StandardOpenOption}

import scala.collection.mutable

import org.scalatest.ResourcefulReporter
import org.scalatest.events.{
  Event,
  RunAborted,
  RunCompleted,
  RunStopped,
  TestCanceled,
  TestFailed,
  TestPending,
  TestStarting,
  TestSucceeded,
}

/** Writes configuration-aware ScalaTest timing events as JSON Lines.
  *
  * A start record is flushed before each test runs. If the worker is killed, the
  * report generator can therefore identify the test that never produced a
  * matching completion record.
  */
final class IntegrationTimingReporter private[integration] (
    outputDirectory: Path,
    forcedOutputPath: Option[Path],
    forcedConfiguration: Option[String])
    extends ResourcefulReporter {
  import IntegrationTimingReporter._

  private val startedAt = mutable.Map.empty[TestId, Long]
  private val writers = mutable.Map.empty[String, BufferedWriter]
  private var closed = false

  /** Constructor used by focused reporter tests. */
  private[integration] def this(outputPath: Path, configuration: String) =
    this(outputPath.getParent, Some(outputPath), Some(configuration))

  /** Constructor used to test configuration routing without changing process environment. */
  private[integration] def this(outputDirectory: Path) =
    this(outputDirectory, None, None)

  /** Public no-argument constructor required by ScalaTest's `-C` option. */
  def this() = this(
      IntegrationTimingReporter.defaultOutputDirectory(),
      None,
      None,
  )

  override def apply(event: Event): Unit = synchronized {
    if (!closed) {
      event match {
        case event: TestStarting =>
          val (configuration, suiteName) = configurationAndSuiteName(event.suiteName)
          val id = TestId(configuration, event.suiteId, event.testName)
          startedAt.put(id, event.timeStamp)
          write(
              configuration,
              ujson.Obj(
                  "schemaVersion" -> SchemaVersion,
                  "event" -> "started",
                  "configuration" -> configuration,
                  "suiteId" -> event.suiteId,
                  "suiteName" -> suiteName,
                  "testName" -> event.testName,
                  "timestampEpochMillis" -> ujson.Num(event.timeStamp.toDouble),
              ))

        case event: TestSucceeded =>
          finish(event.suiteId, event.suiteName, event.testName, "succeeded", event.duration, event.timeStamp)
        case event: TestFailed =>
          finish(event.suiteId, event.suiteName, event.testName, "failed", event.duration, event.timeStamp)
        case event: TestCanceled =>
          finish(event.suiteId, event.suiteName, event.testName, "canceled", event.duration, event.timeStamp)
        case event: TestPending =>
          finish(event.suiteId, event.suiteName, event.testName, "pending", event.duration, event.timeStamp)

        case _: RunCompleted | _: RunAborted | _: RunStopped => dispose()
        case _                                              => ()
      }
    }
  }

  override def dispose(): Unit = synchronized {
    if (!closed) {
      closed = true
      writers.values.foreach(_.close())
      writers.clear()
    }
  }

  private def finish(
      suiteId: String,
      suiteName: String,
      testName: String,
      status: String,
      reportedDuration: Option[Long],
      timestamp: Long): Unit = {
    val (configuration, unqualifiedSuiteName) = configurationAndSuiteName(suiteName)
    val id = TestId(configuration, suiteId, testName)
    val measuredDuration = startedAt.remove(id).map(start => math.max(0L, timestamp - start))
    val duration = reportedDuration.orElse(measuredDuration).getOrElse(0L)
    write(
        configuration,
        ujson.Obj(
            "schemaVersion" -> SchemaVersion,
            "event" -> "finished",
            "configuration" -> configuration,
            "suiteId" -> suiteId,
            "suiteName" -> unqualifiedSuiteName,
            "testName" -> testName,
            "status" -> status,
            "timestampEpochMillis" -> ujson.Num(timestamp.toDouble),
            "durationMillis" -> ujson.Num(duration.toDouble),
        ))
  }

  private def write(configuration: String, record: ujson.Obj): Unit = {
    val outputPath = forcedOutputPath.getOrElse(outputDirectory.resolve(s"$configuration.jsonl"))
    val writer = writers.getOrElseUpdate(configuration, open(outputPath))
    writer.write(record.render())
    writer.newLine()
    writer.flush()
  }

  private def configurationAndSuiteName(suiteName: String): (String, String) = {
    forcedConfiguration
      .map(_ -> suiteName)
      .getOrElse {
        ConfigurationIds
          .collectFirst {
            case configuration if suiteName.endsWith(s" [$configuration]") =>
              configuration -> suiteName.stripSuffix(s" [$configuration]")
          }
          .getOrElse("general" -> suiteName)
      }
  }
}

private[integration] object IntegrationTimingReporter {
  val SchemaVersion = 1
  val TimingDirectoryProperty = "apalache.cli.test.timing-dir"

  private case class TestId(configuration: String, suiteId: String, testName: String)

  private val ConfigurationIds = IntegrationTestConfiguration.values.map(_.id)

  private[integration] def defaultOutputDirectory(): Path = {
    sys.env
      .get("APALACHE_CLI_TEST_TIMING_DIR")
      .filter(_.nonEmpty)
      .orElse(Option(System.getProperty(TimingDirectoryProperty)).filter(_.nonEmpty))
      .map(Paths.get(_))
      .getOrElse(Paths.get("target", "cli-integration-timings"))
  }

  private def open(outputPath: Path): BufferedWriter = {
    Option(outputPath.getParent).foreach(Files.createDirectories(_))
    try {
      Files.newBufferedWriter(
          outputPath,
          StandardCharsets.UTF_8,
          StandardOpenOption.CREATE,
          StandardOpenOption.TRUNCATE_EXISTING,
          StandardOpenOption.WRITE,
      )
    } catch {
      case exception: IOException =>
        throw new IllegalStateException(s"Could not open integration-test timing report $outputPath", exception)
    }
  }
}
