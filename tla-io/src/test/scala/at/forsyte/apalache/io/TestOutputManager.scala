package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.{CommandInitializationOptions, CommonOptions}
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

import java.nio.file.{Files, Path}
import java.util.concurrent.{Callable, CyclicBarrier, Executors}
import scala.jdk.CollectionConverters._
import scala.util.Using

@RunWith(classOf[JUnitRunner])
class TestOutputManager extends AnyFunSuite {

  private case class Observation(outDir: Path, runDir: Path, source: String)

  test("calls outside a scope fail with a useful error") {
    val error = intercept[IllegalStateException](OutputManager.isConfigured)
    assert(error.getMessage.contains("OutputManager.withScope"))
    assert(!OutputManager.withProfilingWriter(_ => fail("unbound profiling writer should be disabled")))
    assert(OutputManager.Names.RunFile == "run.txt")
  }

  test("fresh scopes do not retain paths or source lines") {
    withTempDirectory("output-manager-sequential") { root =>
      val firstOut = root.resolve("first-out")
      val firstCustom = root.resolve("first-custom")
      val firstSource = InputSource.StringSource("---- MODULE First ----\n====")

      OutputManager.withScope {
        assert(!OutputManager.isConfigured)
        assert(OutputManager.getAllSrc.isEmpty)
        OutputManager.configure(initialization("first", firstOut, Some(firstCustom), writeIntermediate = true,
            Some(firstSource)))
        OutputManager.initSourceLines(firstSource)

        assert(OutputManager.isConfigured)
        assert(OutputManager.outDir == firstOut.resolve("first").toAbsolutePath)
        assert(OutputManager.customRunDirPathOpt.contains(firstCustom.toAbsolutePath))
        assert(OutputManager.getAllSrc.contains("---- MODULE First ----\n===="))
        assert(OutputManager.withWriterInIntermediateDir("first.txt")(_.println("first")))
        assert(OutputManager.withWriterInRunDir("result.txt")(_.println("first")))
        assert(Files.exists(OutputManager.runDir.resolve("result.txt")))
        assert(Files.exists(firstCustom.resolve("result.txt")))
      }

      val secondOut = root.resolve("second-out")
      val secondSource = InputSource.StringSource("---- MODULE Second ----\n====")
      OutputManager.withScope {
        assert(!OutputManager.isConfigured)
        assert(OutputManager.runDirPathOpt.isEmpty)
        assert(OutputManager.customRunDirPathOpt.isEmpty)
        assert(OutputManager.getAllSrc.isEmpty)

        OutputManager.configure(initialization("second", secondOut, None, writeIntermediate = false,
            Some(secondSource)))
        OutputManager.initSourceLines(secondSource)

        assert(OutputManager.outDir == secondOut.resolve("second").toAbsolutePath)
        assert(OutputManager.customRunDirPathOpt.isEmpty)
        assert(OutputManager.getAllSrc.contains("---- MODULE Second ----\n===="))
        assert(!OutputManager.withWriterInIntermediateDir("second.txt")(_ => ()))
      }
    }
  }

  test("nested and exceptional scopes restore the previous binding") {
    withTempDirectory("output-manager-nested") { root =>
      OutputManager.withScope {
        OutputManager.configure(initialization("outer", root.resolve("outer")))
        val outerDir = OutputManager.outDir

        OutputManager.withScope {
          assert(!OutputManager.isConfigured)
          OutputManager.configure(initialization("inner", root.resolve("inner")))
          assert(OutputManager.outDir != outerDir)
        }

        assert(OutputManager.outDir == outerDir)
      }

      intercept[RuntimeException] {
        OutputManager.withScope {
          throw new RuntimeException("boom")
        }
      }
      intercept[IllegalStateException](OutputManager.isConfigured)
    }
  }

  test("captured scopes isolate concurrent configuration and can be rebound on worker threads") {
    withTempDirectory("output-manager-concurrent") { root =>
      val firstScope = OutputManager.withScope(OutputManager.captureScope())
      val secondScope = OutputManager.withScope(OutputManager.captureScope())
      val barrier = new CyclicBarrier(2)
      val executor = Executors.newFixedThreadPool(2)

      def task(
          scope: OutputManager.Scope,
          command: String,
          sourceText: String): Callable[Observation] =
        () => scope.run {
          val source = InputSource.StringSource(sourceText)
          OutputManager.configure(initialization(command, root.resolve(s"$command-out"), source = Some(source)))
          OutputManager.initSourceLines(source)
          barrier.await()
          Observation(OutputManager.outDir, OutputManager.runDir, OutputManager.getAllSrc.get)
        }

      try {
        val first = executor.submit(task(firstScope, "first", "---- MODULE First ----\n===="))
        val second = executor.submit(task(secondScope, "second", "---- MODULE Second ----\n===="))
        val firstResult = first.get()
        val secondResult = second.get()

        assert(firstResult.outDir == root.resolve("first-out/first").toAbsolutePath)
        assert(secondResult.outDir == root.resolve("second-out/second").toAbsolutePath)
        assert(firstResult.runDir.startsWith(firstResult.outDir))
        assert(secondResult.runDir.startsWith(secondResult.outDir))
        assert(firstResult.source.contains("MODULE First"))
        assert(secondResult.source.contains("MODULE Second"))
      } finally {
        executor.shutdownNow()
      }
    }
  }

  private def initialization(
      command: String,
      outDir: Path,
      runDir: Option[Path] = None,
      writeIntermediate: Boolean = false,
      source: Option[InputSource] = None): CommandInitializationOptions =
    CommandInitializationOptions(
        command,
        CommonOptions(
            debug = false,
            features = Nil,
            outDir = outDir,
            profiling = false,
            runDir = runDir,
            smtprof = false,
            writeIntermediate = writeIntermediate,
        ),
        source,
    )

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
