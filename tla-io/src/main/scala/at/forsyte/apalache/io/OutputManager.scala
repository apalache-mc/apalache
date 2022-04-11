package at.forsyte.apalache.io

import com.typesafe.scalalogging.LazyLogging

import java.io.{File, FileWriter, PrintWriter}
import java.nio.file.{Files, Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

import scala.io.Source

/**
 * The OutputManager is the central source of truth, for all IO related locations. Any IO operation should request
 * read/write target paths from this object.
 */
object OutputManager extends LazyLogging {

  object Names {
    val IntermediateFoldername = "intermediate"
    val RunFile = "run.txt"
  }
  import Names._

  // TODO RM once OutputManager isn't a singleton
  private var cfg: ApalacheConfig = ApalacheConfig()
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

  // Should be called only if input is a .tla file
  def initSourceLines(file: File): Unit =
    if (sourceLinesOpt.isEmpty) {
      val src = Source.fromFile(file)
      try sourceLinesOpt = Some(src.getLines().toIndexedSeq)
      finally src.close()
    }

  def getLineInSrc(n: Int): Option[String] = sourceLinesOpt.map { _(n) }
  def getAllSrc: Option[String] = sourceLinesOpt.map { _.mkString("\n").trim }

  private def setOutDir(base: Path, namespace: String): Unit = {
    outDirOpt = Some(base.resolve(namespace).toAbsolutePath())
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
   * @throws IllegalStateException
   *   if called before OutputManager is configured: this is considered an implementator error
   */
  def outDir: Path = {
    outDirOpt.getOrElse(throw new IllegalStateException("out-dir is not configured"))
  }

  /**
   * Accessor for the configured run directory.
   *
   * @throws IllegalStateException
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
    if (!((f.exists() && f.isDirectory()) || f.mkdirs())) {
      throw new ConfigurationError(s"Could not find or create directory: ${f.getCanonicalPath}.")
    }
  }

  // Sets the customRunDir, if one is given, otherwise is noop
  private def setCustomRunDir(fopt: Option[File]): Unit = {
    fopt.foreach { f =>
      val dir = f.toPath().toAbsolutePath()
      customRunDirOpt = Some(dir)
      ensureDirExists(dir)
    }
  }

  /**
   * Configure OutputManager, with cli configuration taking precedence over the configuration file
   */
  def configure(config: ApalacheConfig): Unit = {
    // Replace the default config used for initialiation with the config loaded on startup
    cfg = config

    val fileName = cfg.file
      .getOrElse(throw new IllegalStateException("OutputManager configured without file"))
      .getName

    setOutDir(cfg.outDir.toPath(), fileName)
    ensureDirExists(outDir)
    createRunDirectory()
    setCustomRunDir(config.runDir)

    if (cfg.writeIntermediate) {
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
    printWriter(base.toFile(), fileParts: _*)
  }

  /**
   * Create a PrintWriter to the file formed by appending `fileParts` to the `base` file
   *
   * E.g., to create a writer to the file `foo/bar/bas.json`:
   *
   * val w = printWriter("foo", "bar", "baz.json")
   */
  def printWriter(base: String, fileParts: String*): PrintWriter = {
    printWriter(Paths.get(base), fileParts: _*)
  }

  /** Apply f to the writer w, being sure to close w */
  private def withWriter(f: PrintWriter => Unit)(w: PrintWriter) = {
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
    runDirOpt
      .map { runDir =>
        writeToDir(runDir)
        customRunDirOpt.foreach(writeToDir)
        true
      }
      .getOrElse(false)
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
    intermediateDirOpt
      .map { dir =>
        writeToDir(dir)
        customIntermediateRunDir.foreach(writeToDir)
        true
      }
      .getOrElse(false)
  }

  /**
   * Conditionally write into "profile-rules.txt", depending on whether the `profiling` config is set
   */
  def withProfilingWriter(f: PrintWriter => Unit): Boolean = {
    if (cfg.profiling) {
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
    val src = Source.fromFile(file)
    try src.mkString.trim
    finally src.close()
  }

  /**
   * Calls `readFileIntoString` relative to the run directory
   */
  def readContentsOfFileInRunDir(filename: String): Option[String] = runDirPathOpt
    .map { runDir =>
      readFileIntoString(new File(runDir.toFile, filename))
    }
}
