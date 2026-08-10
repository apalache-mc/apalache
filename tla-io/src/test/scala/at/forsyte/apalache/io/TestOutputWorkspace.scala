package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.{CommandInitializationOptions, CommonOptions}
import org.scalatest.funsuite.AnyFunSuite

import java.io.IOException
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._
import scala.util.Using

class TestOutputWorkspace extends AnyFunSuite {

  test("OutputWorkspace instances keep their output state isolated") {
    withTempDirectory { root =>
      val additionalA = root.resolve("additional-a")
      val additionalB = root.resolve("additional-b")
      val workspaceA = makeWorkspace(root, additionalA)
      val workspaceB = makeWorkspace(root, additionalB)

      assert(workspaceA.runDir != workspaceB.runDir)
      workspaceA.withWriterInRunDir("same.txt")(_.write("A"))
      workspaceB.withWriterInRunDir("same.txt")(_.write("B"))

      assert(Files.readString(workspaceA.runDir.resolve("same.txt"), StandardCharsets.UTF_8) == "A")
      assert(Files.readString(workspaceB.runDir.resolve("same.txt"), StandardCharsets.UTF_8) == "B")
      assert(Files.readString(additionalA.resolve("same.txt"), StandardCharsets.UTF_8) == "A")
      assert(Files.readString(additionalB.resolve("same.txt"), StandardCharsets.UTF_8) == "B")

      workspaceA.withWriterInIntermediateDir("intermediate.txt")(_.write("A"))
      assert(Files.exists(workspaceA.runDir.resolve(OutputWorkspace.IntermediateDirName).resolve("intermediate.txt")))
      assert(Files.exists(additionalA.resolve(OutputWorkspace.IntermediateDirName).resolve("intermediate.txt")))

      assert(workspaceA.withProfilingWriter(_.write("profile-a")))
      assert(workspaceB.withProfilingWriter(_.write("profile-b")))

      def readString(workspace: OutputWorkspace) = {
        val path = OutputWorkspace.ruleProfilePath(workspace.runDir)
        Files.readString(path, StandardCharsets.UTF_8)
      }
      assert(readString(workspaceA) == "profile-a")
      assert(readString(workspaceB) == "profile-b")

      val scopedFile = root.resolve("scoped.txt")
      val walz = "An der schönen blauen Donau"
      workspaceA.withWriter(scopedFile)(_.write(walz))
      assert(Files.readString(scopedFile, StandardCharsets.UTF_8) == walz)

      val openFile = root.resolve("open.txt")
      Using.resource(workspaceA.openWriter(openFile)) { openWriter =>
        openWriter.write("long-lived")
      }
      assert(Files.readString(openFile, StandardCharsets.UTF_8) == "long-lived")

      val failedFile = root.resolve("failed.txt")
      assertThrows[IOException] {
        workspaceA.withWriter(failedFile) { writer =>
          writer.close()
          writer.write("fail")
        }
      }
    }
  }

  private def makeWorkspace(root: Path, additionalRunDir: Path): OutputWorkspace = {
    val common = CommonOptions(
        debug = false,
        features = Nil,
        outDir = root.resolve("out"),
        profiling = true,
        runDir = Some(additionalRunDir),
        smtprof = false,
        writeIntermediate = true,
    )
    new OutputWorkspace(CommandInitializationOptions("check", common, None))
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
