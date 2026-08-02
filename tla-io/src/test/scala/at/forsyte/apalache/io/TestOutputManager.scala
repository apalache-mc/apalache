package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.{CommandInitializationOptions, CommonOptions}
import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

class TestOutputManager extends AnyFunSuite {

  test("OutputManager instances keep their output state isolated") {
    withTempDirectory { root =>
      val additionalA = root.resolve("additional-a")
      val additionalB = root.resolve("additional-b")
      val managerA = makeManager(root, additionalA)
      val managerB = makeManager(root, additionalB)

      assert(managerA.runDir != managerB.runDir)
      managerA.withWriterInRunDir("same.txt")(_.print("A"))
      managerB.withWriterInRunDir("same.txt")(_.print("B"))

      assert(Files.readString(managerA.runDir.resolve("same.txt"), StandardCharsets.UTF_8) == "A")
      assert(Files.readString(managerB.runDir.resolve("same.txt"), StandardCharsets.UTF_8) == "B")
      assert(Files.readString(additionalA.resolve("same.txt"), StandardCharsets.UTF_8) == "A")
      assert(Files.readString(additionalB.resolve("same.txt"), StandardCharsets.UTF_8) == "B")

      managerA.withWriterInIntermediateDir("intermediate.txt")(_.print("A"))
      assert(Files.exists(managerA.runDir.resolve(OutputManager.IntermediateDirName).resolve("intermediate.txt")))
      assert(Files.exists(additionalA.resolve(OutputManager.IntermediateDirName).resolve("intermediate.txt")))

      assert(managerA.withProfilingWriter(_.print("profile-a")))
      assert(managerB.withProfilingWriter(_.print("profile-b")))

      def readString(manager: OutputManager) = {
        val path = OutputManager.ruleProfilePath(manager.runDir)
        Files.readString(path, StandardCharsets.UTF_8)
      }
      assert(readString(managerA) == "profile-a")
      assert(readString(managerB) == "profile-b")

      val scopedFile = root.resolve("scoped.txt")
      val walz = "An der schönen blauen Donau"
      managerA.withWriter(scopedFile)(_.print(walz))
      assert(Files.readString(scopedFile, StandardCharsets.UTF_8) == walz)

      val openFile = root.resolve("open.txt")
      val openWriter = managerA.openWriter(openFile)
      try {
        openWriter.print("long-lived")
        openWriter.flush()
        assert(Files.readString(openFile, StandardCharsets.UTF_8) == "long-lived")
      } finally {
        openWriter.close()
      }
    }
  }

  private def makeManager(root: Path, additionalRunDir: Path): OutputManager = {
    val common = CommonOptions(
        debug = false,
        features = Nil,
        outDir = root.resolve("out"),
        profiling = true,
        runDir = Some(additionalRunDir),
        smtprof = false,
        writeIntermediate = true,
    )
    new OutputManager(CommandInitializationOptions("check", common, None))
  }

  private def withTempDirectory(test: Path => Unit): Unit = {
    val root = Files.createTempDirectory("output-manager-test")
    try test(root)
    finally {
      val paths = Files.walk(root)
      try paths.iterator().asScala.toSeq.reverse.foreach(Files.delete)
      finally paths.close()
    }
  }
}
