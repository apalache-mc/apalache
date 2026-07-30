package at.forsyte.apalache.io.config

import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

class TestApalacheConfigLoader extends AnyFunSuite {
  test("an explicit file is the only selected file and primary values override it") {
    withTempDirectories { (work, home) =>
      write(work.resolve(".apalache.json"), "not json")
      writeGlobal(home, "not json")
      val explicit = work.resolve("selected.json")
      write(
          explicit,
          """{"out-dir":"selected","checker":{"length":2,"tuning":{"selected":"1","shared":"selected"}}}""",
      )
      val primary = ApalacheConfigJsonParser
        .parse("""{"checker":{"length":3,"tuning":{"primary":"1","shared":"primary"}}}""")
        .requireValue()
        .copy(context = RunContextPatch(command = Some("check"), configFile = Some(explicit)))

      val result = new ApalacheConfigLoader(work, home).load(primary)

      assert(result.isSuccess)
      val merged = result.requireValue()
      assert(merged.common.outDir.get.toString == "selected")
      assert(merged.checker.length.contains(3))
      assert(merged.checker.tuning.contains(Map("selected" -> "1", "primary" -> "1", "shared" -> "primary")))
    }
  }

  test("a cwd-local file is selected without reading the user-wide file") {
    withTempDirectories { (work, home) =>
      write(work.resolve(".apalache.json"), """{"run-dir":"local-run"}""")
      writeGlobal(home, "not json")

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "local-run")
    }
  }

  test("does not traverse parent directories and uses the user-wide file instead") {
    withTempDirectories { (work, home) =>
      val child = Files.createDirectory(work.resolve("child"))
      write(work.resolve(".apalache.json"), """{"run-dir":"parent-run"}""")
      writeGlobal(home, """{"run-dir":"global-run"}""")

      val result = new ApalacheConfigLoader(child, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "global-run")
    }
  }

  test("uses the user-wide file only when no explicit or cwd-local file exists") {
    withTempDirectories { (work, home) =>
      writeGlobal(home, """{"run-dir":"global-run"}""")

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "global-run")
    }
  }

  test("an invalid selected user-wide file is reported") {
    withTempDirectories { (work, home) =>
      writeGlobal(home, "not json")

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(!result.isSuccess)
      assert(result.errors.exists(_.contains(".tlaplus")))
    }
  }

  test("returns the primary configuration when no file is selected") {
    withTempDirectories { (work, home) =>
      val primary = ApalacheConfig.empty.withCommand("check")

      val result = new ApalacheConfigLoader(work, home).load(primary)

      assert(result.isSuccess)
      assert(result.requireValue() == primary)
    }
  }

  test("an invalid cwd-local file fails instead of falling back to the user-wide file") {
    withTempDirectories { (work, home) =>
      write(work.resolve(".apalache.json"), "not json")
      writeGlobal(home, """{"run-dir":"global-run"}""")

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(!result.isSuccess)
      assert(result.errors.exists(_.contains(".apalache.json")))
    }
  }

  test("a missing explicit file fails without attempting discovery") {
    withTempDirectories { (work, home) =>
      write(work.resolve(".apalache.json"), """{"run-dir":"local-run"}""")
      writeGlobal(home, """{"run-dir":"global-run"}""")
      val missing = work.resolve("missing.json")
      val primary = ApalacheConfig(context = RunContextPatch(
          command = Some("check"),
          configFile = Some(missing),
      ))

      val result = new ApalacheConfigLoader(work, home).load(primary)

      assert(!result.isSuccess)
      assert(result.errors.exists(error =>
            error.contains("Configuration file not found") && error.contains("missing.json")))
    }
  }

  test("automatically discovered legacy filenames are ignored") {
    withTempDirectories { (work, home) =>
      write(work.resolve(".apalache.cfg"), "not json")
      val globalDirectory = Files.createDirectory(home.resolve(".tlaplus"))
      write(globalDirectory.resolve("apalache.cfg"), "not json")
      write(globalDirectory.resolve("apalache.json"), """{"run-dir":"global-run"}""")

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "global-run")
    }
  }

  test("a legacy file beside a cwd-local JSON file does not prevent selecting the JSON file") {
    withTempDirectories { (work, home) =>
      write(work.resolve(".apalache.cfg"), "not json")
      write(work.resolve(".apalache.json"), """{"run-dir":"local-run"}""")

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "local-run")
    }
  }

  test("rejects an explicitly selected application config with a .cfg filename") {
    withTempDirectories { (work, home) =>
      val explicit = work.resolve("selected.cfg")
      write(explicit, """{"run-dir":"legacy-run"}""")
      val primary = ApalacheConfig(context = RunContextPatch(
          command = Some("check"),
          configFile = Some(explicit),
      ))

      val result = new ApalacheConfigLoader(work, home).load(primary)

      assert(!result.isSuccess)
      assert(result.errors.exists(error => error.contains("selected.cfg") && error.contains("selected.json")))
    }
  }

  test("config-file inside the selected file does not trigger recursive loading") {
    withTempDirectories { (work, home) =>
      write(
          work.resolve(".apalache.json"),
          """{"config-file":"missing.json","run-dir":"local-run"}""",
      )

      val result = new ApalacheConfigLoader(work, home).load(ApalacheConfig.empty.withCommand("check"))

      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "local-run")
    }
  }

  private def writeGlobal(home: Path, contents: String): Unit = {
    val directory = home.resolve(".tlaplus")
    Files.createDirectories(directory)
    write(directory.resolve("apalache.json"), contents)
  }

  private def write(path: Path, contents: String): Unit =
    Files.writeString(path, contents, StandardCharsets.UTF_8)

  private def withTempDirectories(test: (Path, Path) => Unit): Unit = {
    val root = Files.createTempDirectory("apalache-config-test")
    val work = Files.createDirectory(root.resolve("work"))
    val home = Files.createDirectory(root.resolve("home"))
    try test(work, home)
    finally {
      val paths = Files.walk(root)
      try paths.iterator().asScala.toSeq.reverse.foreach(Files.delete)
      finally paths.close()
    }
  }
}
