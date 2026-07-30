package at.forsyte.apalache.io.config

import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters._

class TestApalacheConfigLoader extends AnyFunSuite {
  test("rejects .apalache.cfg when .apalache.json exists beside it") {
    withTempDirectories { (work, home) =>
      Files.writeString(
          work.resolve(".apalache.json"),
          """{"run-dir":"json-run"}""",
          StandardCharsets.UTF_8,
      )
      Files.writeString(
          work.resolve(".apalache.cfg"),
          """{"run-dir":"legacy-run"}""",
          StandardCharsets.UTF_8,
      )

      val result = new ApalacheConfigLoader(work, home).loadWithFallbacks(ApalacheConfig.empty.withCommand("check"))
      assert(!result.isSuccess)
      assert(result.errors.exists(error => error.contains(".apalache.cfg") && error.contains("Remove it")))
    }
  }

  test("rejects a discovered .apalache.cfg even when it contains strict JSON") {
    withTempDirectories { (work, home) =>
      Files.writeString(
          work.resolve(".apalache.cfg"),
          """{"run-dir":"legacy-run"}""",
          StandardCharsets.UTF_8,
      )

      val result = new ApalacheConfigLoader(work, home).loadWithFallbacks(ApalacheConfig.empty.withCommand("check"))
      assert(!result.isSuccess)
      assert(result.errors.exists(error => error.contains(".apalache.cfg") && error.contains(".apalache.json")))
    }
  }

  test("rejects an explicit application config with a .cfg filename") {
    withTempDirectories { (work, home) =>
      val explicit = work.resolve("selected.cfg")
      Files.writeString(
          explicit,
          """{"run-dir":"legacy-run"}""",
          StandardCharsets.UTF_8,
      )
      val primary = ApalacheConfig(context = RunContextPatch(
          command = Some("check"),
          configFile = Some(explicit),
      ))

      val result = new ApalacheConfigLoader(work, home).loadWithFallbacks(primary)
      assert(!result.isSuccess)
      assert(result.errors.exists(error => error.contains("selected.cfg") && error.contains("selected.json")))
    }
  }

  test("rejects the legacy user-wide application config filename") {
    withTempDirectories { (work, home) =>
      val globalDirectory = Files.createDirectory(home.resolve(".tlaplus"))
      Files.writeString(
          globalDirectory.resolve("apalache.cfg"),
          """{"run-dir":"legacy-run"}""",
          StandardCharsets.UTF_8,
      )

      val result = new ApalacheConfigLoader(work, home).loadWithFallbacks(ApalacheConfig.empty.withCommand("check"))
      assert(!result.isSuccess)
      assert(result.errors.exists(error => error.contains("apalache.cfg") && error.contains("apalache.json")))
    }
  }

  test("applies primary, local, and global precedence in that order") {
    withTempDirectories { (work, home) =>
      val globalDirectory = Files.createDirectory(home.resolve(".tlaplus"))
      Files.writeString(
          globalDirectory.resolve("apalache.json"),
          """{"out-dir":"global","checker":{"length":1,"tuning":{"global":"1","shared":"global"}}}""",
          StandardCharsets.UTF_8,
      )
      Files.writeString(
          work.resolve(".apalache.json"),
          """{"out-dir":"local","checker":{"length":2,"tuning":{"local":"1","shared":"local"}}}""",
          StandardCharsets.UTF_8,
      )
      val primary = ApalacheConfigJsonParser
        .parse("""{"checker":{"length":3,"tuning":{"primary":"1","shared":"primary"}}}""")
        .requireValue()
        .withCommand("check")

      val result = new ApalacheConfigLoader(work, home).loadWithFallbacks(primary)
      assert(result.isSuccess)
      val merged = result.requireValue()
      assert(merged.common.outDir.get.toString == "local")
      assert(merged.checker.length.get == 3)
      assert(merged.checker.tuning.get ==
        Map("global" -> "1", "local" -> "1", "primary" -> "1", "shared" -> "primary"))
    }
  }

  test("an explicit config file replaces local discovery") {
    withTempDirectories { (work, home) =>
      Files.writeString(
          work.resolve(".apalache.json"),
          """{"run-dir":"local-run"}""",
          StandardCharsets.UTF_8,
      )
      val explicit = work.resolve("selected.json")
      Files.writeString(
          explicit,
          """{"run-dir":"selected-run"}""",
          StandardCharsets.UTF_8,
      )
      val primary = ApalacheConfig(context = RunContextPatch(
          command = Some("check"),
          configFile = Some(explicit),
      ))

      val result = new ApalacheConfigLoader(work, home).loadWithFallbacks(primary)
      assert(result.isSuccess)
      assert(result.requireValue().common.runDir.get.toString == "selected-run")
    }
  }

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
