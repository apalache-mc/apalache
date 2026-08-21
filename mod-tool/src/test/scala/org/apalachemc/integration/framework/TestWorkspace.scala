package org.apalachemc.integration.framework

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import java.util.Comparator
import scala.annotation.tailrec
import scala.jdk.CollectionConverters._

/** Owns the isolated filesystem state for one CLI integration scenario. */
final class TestWorkspace private (val root: Path, val repoRoot: Path) extends AutoCloseable {
  val home: Path = Files.createDirectories(root.resolve("home"))
  val temporaryDirectory: Path = Files.createDirectories(root.resolve("tmp"))
  val outDir: Path = Files.createDirectories(root.resolve("out"))

  private val statisticsDirectory = Files.createDirectories(home.resolve(".tlaplus"))
  Files.writeString(statisticsDirectory.resolve("esc.txt"), "NO_STATISTICS\n", StandardCharsets.UTF_8)

  /** Returns a named repository input as a command-line argument. */
  def filename(name: String): String = path(name).toString

  /** Resolves a named repository input as a path. */
  def path(name: String): Path = {
    val resolvedPath = repoRoot.resolve("test").resolve("tla").resolve(name).normalize()
    require(Files.isRegularFile(resolvedPath), s"CLI integration input file does not exist: $resolvedPath")
    resolvedPath
  }

  /** Writes UTF-8 content to a path relative to this workspace. */
  def write(relativePath: String, content: String): Path = {
    val path = root.resolve(relativePath).normalize()
    require(path.startsWith(root), s"Test file escapes its workspace: $relativePath")
    Option(path.getParent).foreach(parent => Files.createDirectories(parent))
    Files.writeString(path, content, StandardCharsets.UTF_8)
  }

  /** Reads a UTF-8 file. */
  def read(path: Path): String = Files.readString(path, StandardCharsets.UTF_8)

  /** Lists regular files below a directory as slash-separated relative paths. */
  def filesBelow(directory: Path): Set[String] = {
    if (!Files.exists(directory)) {
      Set.empty
    } else {
      val paths = Files.walk(directory)
      try {
        paths.iterator().asScala
          .filter(Files.isRegularFile(_))
          .map(path => directory.relativize(path).iterator().asScala.mkString("/"))
          .toSet
      } finally {
        paths.close()
      }
    }
  }

  /** Returns the sole Tool run directory for the given input namespace. */
  def singleRunDirectory(inputName: String): Path = {
    val namespace = outDir.resolve(inputName)
    require(Files.isDirectory(namespace), s"No output namespace exists at $namespace")
    val children = Files.list(namespace)
    try {
      val directories = children.iterator().asScala.filter(Files.isDirectory(_)).toVector
      require(directories.size == 1, s"Expected one run directory below $namespace, found ${directories.mkString(", ")}")
      directories.head
    } finally {
      children.close()
    }
  }

  /** Recursively deletes this workspace. */
  override def close(): Unit = {
    if (Files.exists(root)) {
      val paths = Files.walk(root)
      try {
        paths.sorted(Comparator.reverseOrder()).forEach(Files.deleteIfExists(_))
      } finally {
        paths.close()
      }
    }
  }
}

/** Creates isolated workspaces with optional access to repository input files. */
object TestWorkspace {
  private val RepoRootProperty = "apalache.cli.test.repo-root"

  /** Creates a temporary workspace and locates the repository input files when available. */
  def create(): TestWorkspace = {
    val repoRoot = Option(System.getProperty(RepoRootProperty))
      .map(Paths.get(_))
      .orElse(findRepoRoot(Paths.get(System.getProperty("user.dir"))))
    create(repoRoot)
  }

  /** Creates a temporary workspace using an explicitly supplied repository root. */
  private[integration] def create(configuredRepoRoot: Option[Path]): TestWorkspace = {
    val root = Files.createTempDirectory("apalache-cli-integration-").toAbsolutePath.normalize()
    val repoRoot = configuredRepoRoot.map(_.toAbsolutePath.normalize()).getOrElse(root)
    new TestWorkspace(root, repoRoot)
  }

  /** Finds the nearest ancestor containing this repository's input directory. */
  private[integration] def findRepoRoot(start: Path): Option[Path] = {
    @tailrec
    def search(candidate: Path): Option[Path] = {
      if (candidate == null) {
        None
      } else if (
          Files.isRegularFile(candidate.resolve("build.sbt")) &&
          Files.isDirectory(candidate.resolve("test").resolve("tla"))) {
        Some(candidate)
      } else {
        search(candidate.getParent)
      }
    }

    search(start.toAbsolutePath.normalize())
  }
}
