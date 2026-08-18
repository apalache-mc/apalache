package at.forsyte.apalache.tla

import at.forsyte.apalache.infra.ExitCodes
import at.forsyte.apalache.infra.log.LogbackConfigurator
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import java.nio.file.{Files, Path}
import java.util.concurrent.{Callable, CountDownLatch, Executors, TimeUnit}
import scala.jdk.CollectionConverters._
import scala.util.Using

@RunWith(classOf[JUnitRunner])
class TestConcurrentToolRuns extends AnyFunSuite {

  test("concurrent Tool runs keep intermediate output in their own directories") {
    // Avoid racing SLF4J's one-time provider initialization. Logback itself remains process-global and is not part of
    // the OutputManager isolation contract exercised by this test.
    new LogbackConfigurator(None, None).configureDefaultContext()

    withTempDirectory("concurrent-tool-runs") { root =>
      val firstSource = writeSpec(root, "First", "FirstValue == 1")
      val secondSource = writeSpec(root, "Second", "SecondValue == 2")
      val firstOut = root.resolve("first-out")
      val secondOut = root.resolve("second-out")
      val start = new CountDownLatch(1)
      val executor = Executors.newFixedThreadPool(2)

      def run(source: Path, outDir: Path): Callable[Int] = () => {
        start.await()
        Tool.run(Array(
                "parse",
                s"--out-dir=$outDir",
                "--write-intermediate=true",
                source.toString,
            ))
      }

      try {
        val first = executor.submit(run(firstSource, firstOut))
        val second = executor.submit(run(secondSource, secondOut))
        start.countDown()

        assert(first.get(2, TimeUnit.MINUTES) == ExitCodes.OK)
        assert(second.get(2, TimeUnit.MINUTES) == ExitCodes.OK)

        val firstIntermediate = findFile(firstOut.resolve("First.tla"), "00_OutSanyParser.tla")
        val secondIntermediate = findFile(secondOut.resolve("Second.tla"), "00_OutSanyParser.tla")
        val firstText = Files.readString(firstIntermediate)
        val secondText = Files.readString(secondIntermediate)

        assert(firstText.contains("FirstValue"))
        assert(!firstText.contains("SecondValue"))
        assert(secondText.contains("SecondValue"))
        assert(!secondText.contains("FirstValue"))
      } finally {
        executor.shutdownNow()
      }
    }
  }

  private def writeSpec(root: Path, module: String, declaration: String): Path =
    Files.writeString(
        root.resolve(s"$module.tla"),
        s"---- MODULE $module ----\n$declaration\n====\n",
    )

  private def findFile(root: Path, filename: String): Path =
    Using.resource(Files.walk(root)) { paths =>
      paths.iterator().asScala.find(_.getFileName.toString == filename).getOrElse {
        fail(s"Could not find $filename under $root")
      }
    }

  private def withTempDirectory[A](prefix: String)(body: Path => A): A = {
    val directory = Files.createTempDirectory(prefix)
    try {
      body(directory)
    } finally {
      if (Files.exists(directory)) {
        Using.resource(Files.walk(directory)) { paths =>
          paths.iterator().asScala.toSeq.sortBy(_.getNameCount).reverse.foreach(Files.deleteIfExists)
        }
      }
    }
  }
}
