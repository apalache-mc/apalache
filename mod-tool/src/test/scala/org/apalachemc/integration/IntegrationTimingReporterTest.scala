package org.apalachemc.integration

import java.nio.file.Files

import org.apalachemc.integration.framework.{IntegrationTestBase, IntegrationTimingReporter}
import org.scalatest.events.{Ordinal, TestStarting, TestSucceeded}

class IntegrationTimingReporterTest extends IntegrationTestBase {
  test("the timing reporter flushes versioned start and completion records") {
    val output = workspace.root.resolve("reporter-test.jsonl")
    val reporter = new IntegrationTimingReporter(output, "test-configuration")
    val ordinal = new Ordinal(1)

    reporter(
        TestStarting(
            ordinal,
            "Example suite",
            "example-suite-id",
            Some("example.Suite"),
            "does useful work",
            "does useful work",
            timeStamp = 1000L,
        ))

    val start = ujson.read(Files.readString(output)).obj
    assert(start("schemaVersion").num == 1)
    assert(start("event").str == "started")
    assert(start("configuration").str == "test-configuration")

    reporter(
        TestSucceeded(
            ordinal.next,
            "Example suite",
            "example-suite-id",
            Some("example.Suite"),
            "does useful work",
            "does useful work",
            IndexedSeq.empty,
            duration = Some(250L),
            timeStamp = 1250L,
        ))
    reporter.dispose()

    val records = Files.readAllLines(output)
    assert(records.size() == 2)
    val completion = ujson.read(records.get(1)).obj
    assert(completion("event").str == "finished")
    assert(completion("status").str == "succeeded")
    assert(completion("durationMillis").num == 250)
  }

  test("the timing reporter separates concurrent configuration workers") {
    val outputDirectory = workspace.root.resolve("timings")
    val reporter = new IntegrationTimingReporter(outputDirectory)
    val configurations = Seq("oopsla19-z3", "oopsla19-cvc5", "arrays-z3")

    configurations.zipWithIndex.foreach { case (configuration, index) =>
      val ordinal = new Ordinal(index + 1)
      val suiteName = s"Example suite [$configuration]"
      reporter(
          TestStarting(
              ordinal,
              suiteName,
              "example-suite-id",
              Some("example.Suite"),
              "does useful work",
              "does useful work",
              timeStamp = 1000L,
          ))
      reporter(
          TestSucceeded(
              ordinal.next,
              suiteName,
              "example-suite-id",
              Some("example.Suite"),
              "does useful work",
              "does useful work",
              IndexedSeq.empty,
              duration = Some(250L),
              timeStamp = 1250L,
          ))
    }
    reporter.dispose()

    configurations.foreach { configuration =>
      val records = Files.readAllLines(outputDirectory.resolve(s"$configuration.jsonl"))
      assert(records.size() == 2)
      records.forEach { record =>
        val json = ujson.read(record).obj
        assert(json("configuration").str == configuration)
        assert(json("suiteName").str == "Example suite")
      }
    }
  }
}
