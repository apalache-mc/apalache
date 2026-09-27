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

  private case class Observation(runDir: Path, contents: String)

  test("required access outside a configured scope fails and optional output is disabled") {
    val error = intercept[IllegalStateException](OutputManager.runDir)
    assert(error.getMessage.contains("OutputManager.withScope"))
    assert(!OutputManager.withProfilingWriter(_ => fail("unbound profiling writer should be disabled")))
    assert(OutputManager.openLongLivedWritersInRunDirs("unbound.txt").isEmpty)
    assert(!OutputManager.withWriterInRunDir("unbound.txt")(_ => fail("unbound run output is disabled")))
    OutputManager.withWriterInIntermediateDir("unbound.txt")(_ => fail("unbound intermediate output is disabled"))
    assert(OutputManager.RunFile == "run.txt")
  }

  test("a workspace owns and mirrors its filesystem output") {
    withTempDirectory("output-workspace-filesystem") { root =>
      val additional = root.resolve("additional")
      val workspace = new OutputManager(
          initialization(
              "check",
              root.resolve("out"),
              Some(additional),
              writeIntermediate = true,
              profiling = true,
          )
      )

      assert(workspace.runDir.getParent == root.resolve("out/check").toAbsolutePath)
      assert(workspace.additionalRunDir.contains(additional.toAbsolutePath))
      assert(workspace.pathInRunDir("nested", "file.txt") == workspace.runDir.resolve("nested/file.txt"))

      workspace.withWriterInRunDir("result.txt")(_.print("result"))
      assert(Files.readString(workspace.pathInRunDir("result.txt")) == "result")
      assert(Files.readString(additional.resolve("result.txt")) == "result")

      workspace.withWriterInIntermediateDir("intermediate.txt")(_.print("intermediate"))
      assert(Files.readString(workspace.pathInRunDir("intermediate/intermediate.txt")) == "intermediate")
      assert(Files.readString(additional.resolve("intermediate/intermediate.txt")) == "intermediate")

      assert(workspace.withProfilingWriter(_.print("profile")))
      assert(Files.readString(workspace.pathInRunDir(OutputManager.RuleProfileFile)) == "profile")

      val external = root.resolve("external.txt")
      workspace.withWriterOutsideWorkspace(external)(_.print("external"))
      assert(Files.readString(external) == "external")

      val longLivedWriters = workspace.openLongLivedWritersInRunDirs("long-lived.txt").toList
      try {
        longLivedWriters.foreach { writer =>
          writer.print("long-lived")
          writer.flush()
        }
        assert(Files.readString(workspace.pathInRunDir("long-lived.txt")) == "long-lived")
        assert(Files.readString(additional.resolve("long-lived.txt")) == "long-lived")
      } finally {
        longLivedWriters.foreach(_.close())
      }

      val disabled = new OutputManager(initialization("disabled", root.resolve("out")))
      disabled.withWriterInIntermediateDir("disabled.txt")(_ => fail("intermediate output should be disabled"))
      assert(!disabled.withProfilingWriter(_ => fail("profiling should be disabled")))
      assert(!Files.exists(disabled.pathInRunDir(OutputManager.IntermediateDirName)))
    }
  }

  test("fresh scopes do not retain a previously configured workspace") {
    withTempDirectory("output-workspace-sequential") { root =>
      val firstRunDir = OutputManager.withScope {
        OutputManager.configure(initialization("first", root.resolve("first-out")))
        OutputManager.withWriterInRunDir("result.txt")(_.print("first"))
        OutputManager.runDir
      }

      OutputManager.withScope {
        intercept[IllegalStateException](OutputManager.runDir)
        OutputManager.configure(initialization("second", root.resolve("second-out")))
        assert(OutputManager.runDir != firstRunDir)
        assert(!Files.exists(OutputManager.pathInRunDir("result.txt")))
      }
    }
  }

  test("nested and exceptional scopes restore the previous binding") {
    withTempDirectory("output-workspace-nested") { root =>
      OutputManager.withScope {
        OutputManager.configure(initialization("outer", root.resolve("outer")))
        val outerDir = OutputManager.runDir

        OutputManager.withScope {
          intercept[IllegalStateException](OutputManager.runDir)
          OutputManager.configure(initialization("inner", root.resolve("inner")))
          assert(OutputManager.runDir != outerDir)
        }

        assert(OutputManager.runDir == outerDir)
      }

      intercept[RuntimeException] {
        OutputManager.withScope {
          throw new RuntimeException("boom")
        }
      }
      intercept[IllegalStateException](OutputManager.runDir)
    }
  }

  test("captured scopes isolate concurrent configuration and can be rebound on worker threads") {
    withTempDirectory("output-workspace-concurrent") { root =>
      val firstScope = OutputManager.withScope(OutputManager.captureScope())
      val secondScope = OutputManager.withScope(OutputManager.captureScope())
      val barrier = new CyclicBarrier(2)
      val executor = Executors.newFixedThreadPool(2)

      def task(scope: OutputManager.Scope, command: String): Callable[Observation] =
        () =>
          scope.run {
            OutputManager.configure(initialization(command, root.resolve(s"$command-out")))
            OutputManager.withWriterInRunDir("same.txt")(_.print(command))
            barrier.await()
            Observation(OutputManager.runDir, Files.readString(OutputManager.pathInRunDir("same.txt")))
          }

      try {
        val first = executor.submit(task(firstScope, "first"))
        val second = executor.submit(task(secondScope, "second"))
        val firstResult = first.get()
        val secondResult = second.get()

        assert(firstResult.runDir.startsWith(root.resolve("first-out/first").toAbsolutePath))
        assert(secondResult.runDir.startsWith(root.resolve("second-out/second").toAbsolutePath))
        assert(firstResult.contents == "first")
        assert(secondResult.contents == "second")
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
      profiling: Boolean = false): CommandInitializationOptions =
    CommandInitializationOptions(
        command,
        CommonOptions(
            debug = false,
            features = Nil,
            outDir = outDir,
            profiling = profiling,
            runDir = runDir,
            smtprof = false,
            writeIntermediate = writeIntermediate,
        ),
        source = None,
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
