package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.CommandInitializationOptions

import java.io.{IOException, PrintWriter}
import java.lang.ScopedValue
import java.nio.file.{Files, Path}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

/**
 * Owns the output locations and writer lifecycle conventions for one Apalache execution.
 *
 * The workspace creates all configured directories during construction and mirrors run output to an additional run
 * directory when requested. See
 * [[https://github.com/apalache-mc/apalache/blob/main/docs/src/adr/009adr-outputs.md ADR-009]] for the output layout.
 */
final class OutputManager(initialization: CommandInitializationOptions) {
  private val groupDir: Path = {
    val groupName = initialization.source match {
      case Some(InputSource.FileSource(path, _)) => path.getFileName.toString
      case _                                     => initialization.command
    }
    findOrCreateDir(initialization.common.outDir.resolve(groupName))
  }

  /** Unique persistent directory for this execution. */
  val runDir: Path = {
    val niceDate = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyy-MM-dd"))
    val niceTime = LocalDateTime.now().format(DateTimeFormatter.ofPattern("HH-mm-ss"))
    Files.createTempDirectory(groupDir, s"${niceDate}T${niceTime}_")
  }

  /** User-selected additional directory to which run output is mirrored. */
  val additionalRunDir: Option[Path] = initialization.common.runDir.map(findOrCreateDir)

  private val intermediateDirOpt: Option[Path] =
    if (initialization.common.writeIntermediate) {
      Some(findOrCreateDir(runDir.resolve(OutputManager.IntermediateDirName)))
    } else {
      None
    }

  private val additionalIntermediateDirOpt: Option[Path] =
    intermediateDirOpt.flatMap(_ =>
      additionalRunDir.map { path =>
        findOrCreateDir(path.resolve(OutputManager.IntermediateDirName))
      })

  /** Resolve `parts` relative to the primary run directory. */
  def pathInRunDir(parts: String*): Path = parts.foldLeft(runDir)(_.resolve(_))

  /**
   * Open writers in the primary and additional run directories. The caller owns and must close every returned writer.
   */
  def openLongLivedWritersInRunDirs(fileName: String): Iterable[PrintWriter] =
    (Some(runDir) ++ additionalRunDir).map(dir => printWriter(dir.resolve(fileName)))

  /** Write below each run directory and close each writer afterward. */
  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    withWriterAt(pathInRunDir(parts: _*))(f)
    additionalRunDir.foreach(withWriterInJointPath(_, parts, f))
  }

  /** Write below each intermediate directory when intermediate output is enabled. */
  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    intermediateDirOpt.foreach { dir =>
      withWriterInJointPath(dir, parts, f)
      additionalIntermediateDirOpt.foreach(withWriterInJointPath(_, parts, f))
    }
  }

  /** Write the rule-profiling report when profiling is enabled. */
  def withProfilingWriter(f: PrintWriter => Unit): Boolean = {
    if (initialization.common.profiling) {
      withWriterInRunDir(OutputManager.RuleProfileFile)(f)
      true
    } else {
      false
    }
  }

  /** Write to an arbitrary path outside this workspace and close the writer afterward. */
  def withWriterOutsideWorkspace(path: Path)(f: PrintWriter => Unit): Unit = withWriterAt(path)(f)

  private def printWriter(path: Path): PrintWriter = new PrintWriter(Files.newBufferedWriter(path))

  private def withWriterAt(path: Path)(f: PrintWriter => Unit): Unit = {
    val writer = printWriter(path)
    try {
      f(writer)
    } finally {
      writer.close()
    }
  }

  private def withWriterInJointPath(dir: Path, parts: Seq[String], f: PrintWriter => Unit): Unit = {
    val path = parts.foldLeft(dir)(_.resolve(_))
    withWriterAt(path)(f)
  }

  private def findOrCreateDir(path: Path): Path = {
    val absolutePath = path.toAbsolutePath
    try {
      Files.createDirectories(absolutePath)
    } catch {
      case e: IOException =>
        throw new ConfigurationError(s"Could not find or create directory $absolutePath: ${e.getMessage}")
    }
  }
}

/**
 * Dynamically scoped access to the output workspace for the current tool invocation.
 *
 * A fresh scope starts without a configured workspace. [[configure]] installs one after command initialization has been
 * resolved. [[captureScope]] and [[Scope.run]] propagate the same workspace state to another thread.
 */
object OutputManager {
  final private class State {
    var workspace: Option[OutputManager] = None
  }

  final class Scope private[OutputManager] (private val state: State) {
    def run[A](body: => A): A = withState(state)(body)
  }

  private val currentState: ScopedValue[State] = ScopedValue.newInstance[State]()

  private[io] val IntermediateDirName = "intermediate"
  val RunFile = "run.txt"
  val RuleProfileFile = "profile-rules.txt"

  /** Run `body` with a fresh, initially unconfigured workspace scope. */
  def withScope[A](body: => A): A = new Scope(new State).run(body)

  /** Capture the current workspace scope for explicit propagation to another thread. */
  def captureScope(): Scope = new Scope(state)

  /** Construct and install the workspace for the current scope. */
  def configure(initialization: CommandInitializationOptions): Unit = {
    state.workspace = Some(new OutputManager(initialization))
  }

  def runDir: Path = current.runDir

  def additionalRunDir: Option[Path] = current.additionalRunDir

  def pathInRunDir(parts: String*): Path = current.pathInRunDir(parts: _*)

  /** Optional output for components that may be used outside the tool runtime. */
  def openLongLivedWritersInRunDirs(fileName: String): Iterable[PrintWriter] =
    currentOption.map(_.openLongLivedWritersInRunDirs(fileName)).getOrElse(Iterable.empty)

  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit =
    current.withWriterInRunDir(parts: _*)(f)

  /** Optional output that is disabled until a workspace is configured and intermediate output is enabled. */
  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Unit =
    currentOption.foreach(_.withWriterInIntermediateDir(parts: _*)(f))

  /** Optional output for components that may be used outside the tool runtime. */
  def withProfilingWriter(f: PrintWriter => Unit): Boolean =
    currentOption.exists(_.withProfilingWriter(f))

  def withWriterOutsideWorkspace(path: Path)(f: PrintWriter => Unit): Unit =
    current.withWriterOutsideWorkspace(path)(f)

  private def currentOption: Option[OutputManager] =
    if (currentState.isBound) currentState.get().workspace else None

  private def current: OutputManager =
    currentOption.getOrElse {
      throw new IllegalStateException(
          "OutputManager is not configured in the current scope; " +
            "call OutputManager.withScope { OutputManager.configure(...) ... }"
      )
    }

  private def state: State = {
    if (currentState.isBound) {
      currentState.get()
    } else {
      throw new IllegalStateException(
          "OutputManager is not bound to the current thread; call OutputManager.withScope { ... }"
      )
    }
  }

  // Carrier.run has the same JVM descriptor on Java 21 through Java 25. Carrier.call does not.
  private def withState[A](state: State)(body: => A): A = {
    var result: Option[A] = None
    ScopedValue.where(currentState, state).run(() => result = Some(body))
    result.get
  }
}
