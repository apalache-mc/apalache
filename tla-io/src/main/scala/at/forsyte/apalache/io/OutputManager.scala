package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.{CommandInitializationOptions, CommonOptions}

import java.io.File
import java.io.FileWriter
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import java.nio.charset.StandardCharsets
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.lang.ScopedValue
import scala.jdk.CollectionConverters._

/**
 * Mutable output state for one dynamically scoped tool invocation.
 */
final private class OutputManagerState {
  import OutputManager.Names._

  private var commonOptions: Option[CommonOptions] = None
  // outDirOpt is stored as an expanded and absolute path
  private var outDirOpt: Option[Path] = None
  // This should only be set if the IntermediateFlag is true
  private var intermediateDirOpt: Option[Path] = None
  // The run directory generated automatically inside the outDir
  private var runDirOpt: Option[Path] = None
  // The run directory that users can specify directly through CLI arguments
  private var customRunDirOpt: Option[Path] = None

  // For bug report templates as well as the next iteration of error messages, we will need to reference
  // lines in the original input. This variable stores them.
  private var sourceLinesOpt: Option[IndexedSeq[String]] = None

  // Takes effect only when called on a source that is an existing .tla file or
  // a string representing a .tla spec
  def initSourceLines(source: InputSource): Unit =
    if (sourceLinesOpt.isEmpty && source.exists) {
      source match {
        case InputSource.FileSource(path, _) =>
          sourceLinesOpt = Some(Files.readAllLines(path, StandardCharsets.UTF_8).asScala.toIndexedSeq)
        case value: InputSource.StringSource =>
          sourceLinesOpt = Some(value.content.linesIterator.toIndexedSeq)
      }
    }

  def getAllSrc: Option[String] = sourceLinesOpt.map { _.mkString("\n").trim }

  private def setOutDir(base: Path, namespace: String): Unit = {
    outDirOpt = Some(base.resolve(namespace).toAbsolutePath)
  }

  /* This should only ever be set if the IntermediateFlag is true */
  private def setIntermediateDir(): Unit = {
    intermediateDirOpt = Some(runDir.resolve(IntermediateFoldername))
  }

  /** If this is FALSE, outputs (of any sort) cannot happen, so the tool should exit */
  def isConfigured: Boolean = outDirOpt.nonEmpty

  /** Accessor, read-only */
  def runDirPathOpt: Option[Path] = runDirOpt

  /** Accessor, read-only */
  def customRunDirPathOpt: Option[Path] = customRunDirOpt

  /**
   * Accessor for the configured output directory.
   *
   * @throws java.lang.IllegalStateException
   *   if called before OutputManager is configured: this is considered an implementator error
   */
  def outDir: Path = {
    outDirOpt.getOrElse(throw new IllegalStateException("out-dir is not configured"))
  }

  /**
   * Accessor for the configured run directory.
   *
   * @throws java.lang.IllegalStateException
   *   if called before OutputManager is configured: this is considered an implementator error
   */
  def runDir: Path = {
    runDirOpt.getOrElse(throw new IllegalStateException("run directory does not exist"))
  }

  // The intermdiate output directory in the configured custom
  // run directory
  private def customIntermediateRunDir: Option[Path] = {
    if (intermediateDirOpt.isEmpty) {
      None
    } else {
      customRunDirOpt.map(_.resolve(IntermediateFoldername))
    }
  }

  private def ensureDirExists(path: Path): Unit = {
    val f = path.toFile
    if (!((f.exists() && f.isDirectory) || f.mkdirs())) {
      throw new ConfigurationError(s"Could not find or create directory: ${f.getCanonicalPath}.")
    }
  }

  // Sets the customRunDir, if one is given, otherwise is noop
  private def setCustomRunDir(pathOpt: Option[Path]): Unit = {
    pathOpt.foreach { path =>
      val dir = path.toAbsolutePath()
      customRunDirOpt = Some(dir)
      ensureDirExists(dir)
    }
  }

  /** Configure output paths for a command. */
  def configure(initialization: CommandInitializationOptions): Unit = {
    commonOptions = Some(initialization.common)

    val fileName = initialization.source match {
      case Some(InputSource.FileSource(path, _)) => path.getFileName.toString
      case Some(_: InputSource.StringSource)     => initialization.command
      case None                                  => initialization.command
    }

    setOutDir(initialization.common.outDir, fileName)
    ensureDirExists(outDir)
    createRunDirectory()
    setCustomRunDir(initialization.common.runDir)

    if (initialization.common.writeIntermediate) {
      setIntermediateDir()
      intermediateDirOpt.foreach(ensureDirExists)
      customIntermediateRunDir.foreach(ensureDirExists)
    }
  }

  /* Inside `outputDirOpt`, create a directory for an individual run */
  private def createRunDirectory(): Unit = {
    val nicedate = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"yyyy-MM-dd"))
    val nicetime = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"HH-mm-ss"))
    // prefix for disambiguation
    val rundir = Files.createTempDirectory(outDir, s"${nicedate}T${nicetime}_")
    runDirOpt = Some(rundir)
  }

  /** Create a PrintWriter to the file formed by appending `fileParts` to the `base` file */
  def printWriter(base: File, fileParts: String*): PrintWriter = {
    val file = fileParts.foldLeft(base)((file, part) => new File(file, part))
    new PrintWriter(new FileWriter(file))
  }

  /** Create a PrintWriter to the file formed by appending `fileParts` to the `base` file */
  def printWriter(base: Path, fileParts: String*): PrintWriter = {
    printWriter(base.toFile, fileParts: _*)
  }

  /**
   * Create a PrintWriter to the file formed by appending `fileParts` to the `base` file
   *
   * E.g., to create a writer to the file `foo/bar/bas.json`:
   *
   * val w = printWriter("foo", "bar", "baz.json")
   */
  def printWriter(base: String, fileParts: String*): PrintWriter = {
    printWriter(Path.of(base), fileParts: _*)
  }

  /** Apply f to the writer w, being sure to close w */
  private def withWriter(f: PrintWriter => Unit)(w: PrintWriter): Unit = {
    try {
      f(w)
    } finally {
      w.close()
    }
  }

  def withWriterToFile(file: File)(f: PrintWriter => Unit): Unit = {
    withWriter(f)(printWriter(file))
  }

  /** Applies `f` to a PrintWriter created by appending the `parts` to the `runDir` */
  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Boolean = {
    val writeToDir: Path => Unit = dir => withWriter(f)(printWriter(dir, parts: _*))
    runDirOpt.exists { runDir =>
      writeToDir(runDir)
      customRunDirOpt.foreach(writeToDir)
      true
    }
  }

  /**
   * Conditionally applies a function to a PrintWriter constructed relative to the intermediate directory
   *
   * @param parts
   *   path parts describing a path relative to the intermediate directory (all parents must exist)
   * @param f
   *   a function that will be applied to the `PrintWriter`, if the `IntermediateFlag` is set.
   * @return
   *   `true` if the `IntermediateFlag` is true, and `f` can be applied to the PrintWriter created by appending the
   *   `parts` to the intermediate output dir. Otherwise, `false`.
   */
  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Boolean = {
    val writeToDir: Path => Unit = dir => withWriter(f)(printWriter(dir, parts: _*))
    intermediateDirOpt.exists { dir =>
      writeToDir(dir)
      customIntermediateRunDir.foreach(writeToDir)
      true
    }
  }

  /**
   * Conditionally write into "profile-rules.txt", depending on whether the `profiling` config is set
   */
  def withProfilingWriter(f: PrintWriter => Unit): Boolean = {
    if (commonOptions.exists(_.profiling)) {
      withWriterInRunDir("profile-rules.txt")(f)
      true
    } else {
      false
    }
  }

  /**
   * Reads the contents of a file into a string
   */
  def readFileIntoString(file: File): String = {
    Files.readString(file.toPath, StandardCharsets.UTF_8).trim
  }

  /**
   * Calls `readFileIntoString` relative to the run directory
   */
  def readContentsOfFileInRunDir(filename: String): Option[String] = runDirPathOpt
    .map { runDir =>
      readFileIntoString(new File(runDir.toFile, filename))
    }
}

/**
 * The OutputManager is the central source of truth for all IO-related locations. Its public methods are retained as a
 * compatibility facade, while each invocation stores its mutable state in a [[java.lang.ScopedValue]].
 *
 * Calls must run inside [[withScope]]. Code that hands work to another thread may use [[captureScope]] and
 * [[Scope.run]] to propagate the current manager explicitly.
 */
object OutputManager {

  object Names {
    val IntermediateFoldername = "intermediate"
    val RunFile = "run.txt"
  }

  final class Scope private[OutputManager] (private val state: OutputManagerState) {
    def run[A](body: => A): A = withState(state)(body)
  }

  private val currentState: ScopedValue[OutputManagerState] = ScopedValue.newInstance[OutputManagerState]()

  /** Run `body` with a fresh output manager and restore the previous binding afterwards. */
  def withScope[A](body: => A): A = new Scope(new OutputManagerState).run(body)

  /** Capture the currently bound output manager for explicit propagation to another thread. */
  def captureScope(): Scope = new Scope(current)

  /** Used by low-level components whose output logging is optional when they are used outside the tool runtime. */
  private[apalache] def isBound: Boolean = currentState.isBound

  private def current: OutputManagerState = {
    if (currentState.isBound) {
      currentState.get()
    } else {
      throw new IllegalStateException(
          "OutputManager is not bound to the current thread; call OutputManager.withScope { ... }"
      )
    }
  }

  // Carrier.run has the same JVM descriptor on Java 21 through Java 25. Carrier.call does not.
  private def withState[A](state: OutputManagerState)(body: => A): A = {
    var result: Option[A] = None
    ScopedValue.where(currentState, state).run(() => result = Some(body))
    result.get
  }

  def initSourceLines(source: InputSource): Unit = current.initSourceLines(source)

  def getAllSrc: Option[String] = current.getAllSrc

  def isConfigured: Boolean = current.isConfigured

  def runDirPathOpt: Option[Path] = current.runDirPathOpt

  def customRunDirPathOpt: Option[Path] = current.customRunDirPathOpt

  def outDir: Path = current.outDir

  def runDir: Path = current.runDir

  def configure(initialization: CommandInitializationOptions): Unit = current.configure(initialization)

  def printWriter(base: File, fileParts: String*): PrintWriter = current.printWriter(base, fileParts: _*)

  def printWriter(base: Path, fileParts: String*): PrintWriter = current.printWriter(base, fileParts: _*)

  def printWriter(base: String, fileParts: String*): PrintWriter = current.printWriter(base, fileParts: _*)

  def withWriterToFile(file: File)(f: PrintWriter => Unit): Unit = current.withWriterToFile(file)(f)

  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Boolean =
    current.withWriterInRunDir(parts: _*)(f)

  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Boolean =
    current.withWriterInIntermediateDir(parts: _*)(f)

  def withProfilingWriter(f: PrintWriter => Unit): Boolean =
    currentState.isBound && current.withProfilingWriter(f)

  def readFileIntoString(file: File): String = current.readFileIntoString(file)

  def readContentsOfFileInRunDir(filename: String): Option[String] = current.readContentsOfFileInRunDir(filename)
}
