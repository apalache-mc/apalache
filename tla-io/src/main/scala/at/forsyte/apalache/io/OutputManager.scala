package at.forsyte.apalache.io

import at.forsyte.apalache.infra.passes.WriteablePassOptions

import java.io.{File, FileInputStream}
import java.nio.file.{Files, Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import org.yaml.snakeyaml.Yaml
import java.io.{PrintWriter, FileWriter}

trait OutputManagerConfig {
  // TODO def debug : Boolean
  def outDir: Option[File]
  def writeIntermediate: Option[Boolean]
  def profiling: Option[Boolean]
}

/**
 * The OutputManager is the central source of truth, for all IO related locations.
 * Any IO operation should request read/write target paths from this object.
 */
object OutputManager {

  object Names {
    val OutdirNameInCfg = "out-dir"
    val IntermediateFlag = "write-intermediate"
    val IntermediateFoldername = "intermediate"
    val ProfilingFlag = "profiling"
    val CfgFile = ".tlaplus/apalache-global-config.yml"
    val DefaultOutdir = "_apalache-out"
    val RunFile = "run.txt"
  }
  import Names._

  // outDirOpt is stored as an expanded and absolute path
  private var outDirOpt: Option[Path] = None
  private var runDirOpt: Option[Path] = None
  private var flags: Map[String, Boolean] =
    Map(
        IntermediateFlag -> false,
        ProfilingFlag -> false
    )

  /** If this is FALSE, outputs (of any sort) cannot happen, so the tool should exit */
  def isConfigured: Boolean = outDirOpt.nonEmpty

  /** Accessor, read-only */
  def runDirPathOpt: Option[Path] = runDirOpt

  /**
   * Accessor for the configured run directory.
   *
   * @throws IllegalStateException if called before OutputManager is configured this is considered an implementator error
   */
  def outDir: Path = {
    outDirOpt.getOrElse(throw new IllegalStateException("out-dir is not configured"))
  }

  private def createOutDir(): Unit = {
    val f = outDir.toFile()
    if (!f.exists() && !f.mkdirs()) {
      throw new ConfigurationError(s"Could not find or create directory: ${f.getCanonicalPath}.")
    } else if (!f.isDirectory()) {
      throw new ConfigurationError(s"Configured out-dir is not a directory: ${f.getCanonicalPath}.")
    } else {
      outDirOpt = Some(f.toPath().toAbsolutePath())
    }
  }

  private def expandedFilePath(s: String): Path = {
    val home = System.getProperty("user.home")
    Paths.get(if (s.startsWith("~")) s.replaceFirst("~", home) else s)
  }

  /** Loads the Apalache configuration file from HOME/.tlaplus */
  private def syncFromGlobalConfig(): Unit = {
    val home = System.getProperty("user.home")
    val configFile = new File(home, CfgFile)
    if (configFile.exists()) {
      val yaml = new Yaml
      val configYaml: java.util.Map[String, Any] = yaml.load(new FileInputStream(configFile.getCanonicalPath))

      configYaml.forEach { case (flagName, flagValue) =>
        // `OutdirNameInCfg` is a special flag that governs the output directory
        if (flagName == OutdirNameInCfg) {
          flagValue match {
            case path: String => outDirOpt = Some(expandedFilePath(path))
            case _ =>
              throw new ConfigurationError(
                  s"Flag [$flagName] in [${configFile.getAbsolutePath}] must be a directory path string.")
          }
        } else if (flags.keySet.contains(flagName)) {
          // if not `OutdirNameInCfg`, it must be bool, so check for T/F
          flagValue match {
            case boolVal: Boolean =>
              flags += flagName -> boolVal
            case _ =>
              throw new ConfigurationError(
                  s"Flag [$flagName] in [${configFile.getAbsolutePath}] must be a Boolean value.")
          }
        } else {
          throw new ConfigurationError(
              s"[$flagName] in [${configFile.getAbsolutePath}] is not a valid Apalache parameter.")
        }

      }
    }
    // If `OutdirNameInCfg` is not specified, default to making rundir = <CWD>/_apalache-out/
    if (outDirOpt.isEmpty) {
      outDirOpt = Some(Paths.get(System.getProperty("user.dir"), DefaultOutdir))
    }
  }

  /** Configure OutputManager based on supported CLI flags */
  // TODO(shon): Perhaps we should reworking this object as a class that takes a configuration
  // matching the specification of this trait?
  private def syncFromCli(cli: OutputManagerConfig): Unit = {
    cli.outDir.foreach(d => outDirOpt = Some(d.toPath()))
    cli.writeIntermediate.foreach(flags += IntermediateFlag -> _)
    cli.profiling.foreach(flags += ProfilingFlag -> _)
  }

  /**
   * Configure OutputManager, with cli configuration taking precedence
   * over the configuration file
   */
  def configure(cli: OutputManagerConfig): Unit = {
    syncFromGlobalConfig()
    syncFromCli(cli)
    createOutDir()
  }

  /** lends flags to execute `cmd` conditionally */
  // TODO: remove this once all flag operations are moved into PassOptions
  def doIfFlag(flagName: String)(cmd: => Unit): Unit =
    flags
      .get(flagName)
      .foreach(flag =>
        if (flag) {
          cmd
        }
      )

  /** Inside `outputDirOpt`, create a directory for an individual run */
  def createRunDirectory(specName: String): Unit =
    if (runDirOpt.isEmpty) {
      val nicedate = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"yyyy-MM-dd"))
      val nicetime = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"HH-mm-ss"))
      // prefix for disambiguation
      val rundir = Files.createTempDirectory(outDir, s"${specName}_${nicedate}T${nicetime}_")
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
   *  Create a PrintWriter to the file formed by appending `fileParts` to the `base` file
   *
   * E.g., to create a writer to the file `foo/bar/bas.json`:
   *
   *    val w = printWriter("foo", "bar", "baz.json")
   */
  def printWriter(base: String, fileParts: String*): PrintWriter = {
    printWriter(Paths.get(base), fileParts: _*)
  }

  /**  Apply f to the writer w, being sure to close w */
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
  def withWriterRelativeToRunDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    val w = printWriter(runDirOpt.get, parts: _*)
    withWriter(f)(w)
  }

  /**
   * Conditionally applies a function to a PrintWriter constructed relative to the intermediate directory
   *
   * @param parts path parts describing a path relative to the intermediate directory (all parents must exist)
   * @param f a function that will be applied to the the PrintWriter, if the `IntermediateFlag` is set.
   * @returns `true` if the `IntermediateFlag` is set the output is written, otherwise `false`
   * If the IntermediateFlag is true, then this applies `f` to the PrintWriter
   * created by appending the `parts` to the intermediate output dir, and returns `true`. Otherwise, it is false
   */
  def withWriterRelativeToIntermediateDir(parts: String*)(f: PrintWriter => Unit): Boolean = {
    if (flags(Names.IntermediateFlag)) {
      val intermediateDir = new File(runDirOpt.get.toFile(), Names.IntermediateFoldername)
      if (!intermediateDir.exists()) {
        intermediateDir.mkdir()
      }
      withWriter(f)(printWriter(intermediateDir, parts: _*))
      true
    } else {
      false
    }

  }
}
