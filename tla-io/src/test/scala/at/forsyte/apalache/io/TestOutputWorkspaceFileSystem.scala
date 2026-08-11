package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.{CommandInitializationOptions, CommonOptions}
import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

class TestOutputWorkspaceFileSystem extends AnyFunSuite {

  test("OutputWorkspaceFileSystem instances keep their output state isolated") {
    withTempDirectory { root =>
      val additionalA = root.resolve("additional-a")
      val additionalB = root.resolve("additional-b")
      val workspaceA = makeWorkspace(root, additionalA)
      val workspaceB = makeWorkspace(root, additionalB)

      assert(workspaceA.runDir != workspaceB.runDir)
      workspaceA.withWriterInRunDir("same.txt")(_.print("A"))
      workspaceB.withWriterInRunDir("same.txt")(_.print("B"))

      assert(Files.readString(workspaceA.runDir.resolve("same.txt"), StandardCharsets.UTF_8) == "A")
      assert(Files.readString(workspaceB.runDir.resolve("same.txt"), StandardCharsets.UTF_8) == "B")
      assert(Files.readString(additionalA.resolve("same.txt"), StandardCharsets.UTF_8) == "A")
      assert(Files.readString(additionalB.resolve("same.txt"), StandardCharsets.UTF_8) == "B")

      workspaceA.withWriterInIntermediateDir("intermediate.txt")(_.print("A"))
      assert(Files.exists(workspaceA.runDir.resolve(OutputWorkspace.IntermediateDirName).resolve("intermediate.txt")))
      assert(Files.exists(additionalA.resolve(OutputWorkspace.IntermediateDirName).resolve("intermediate.txt")))

      assert(workspaceA.withProfilingWriter(_.print("profile-a")))
      assert(workspaceB.withProfilingWriter(_.print("profile-b")))

      def readString(workspace: OutputWorkspace) = {
        val path = workspace.pathInRunDir(OutputWorkspace.RuleProfileFile)
        Files.readString(path, StandardCharsets.UTF_8)
      }
      assert(readString(workspaceA) == "profile-a")
      assert(readString(workspaceB) == "profile-b")

      val scopedFile = root.resolve("scoped.txt")
      val walz = "An der schönen blauen Donau"
      workspaceA.withWriterOutsideWorkspace(scopedFile)(_.print(walz))
      assert(Files.readString(scopedFile, StandardCharsets.UTF_8) == walz)

      val openWriters = workspaceA.openLongLivedWritersInRunDirs("open.txt")
      try {
        openWriters.foreach { writer =>
          writer.print("long-lived")
          writer.flush()
        }
        assert(Files.readString(workspaceA.runDir.resolve("open.txt"), StandardCharsets.UTF_8) == "long-lived")
        assert(Files.readString(additionalA.resolve("open.txt"), StandardCharsets.UTF_8) == "long-lived")
      } finally {
        openWriters.foreach(_.close())
      }
    }
  }

  private def makeWorkspace(root: Path, additionalRunDir: Path): OutputWorkspaceFileSystem = {
    val common = CommonOptions(
        debug = false,
        features = Nil,
        outDir = root.resolve("out"),
        profiling = true,
        runDir = Some(additionalRunDir),
        smtprof = false,
        writeIntermediate = true,
    )
    new OutputWorkspaceFileSystem(CommandInitializationOptions("check", common, None))
  }

  private def withTempDirectory(test: Path => Unit): Unit = {
    val root = Files.createTempDirectory("output-workspace-test")
    try test(root)
    finally {
      val paths = Files.walk(root)
      try paths.iterator().asScala.toSeq.reverse.foreach(Files.delete)
      finally paths.close()
    }
  }
}
