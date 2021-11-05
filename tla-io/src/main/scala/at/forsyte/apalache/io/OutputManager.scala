package at.forsyte.apalache.io

import at.forsyte.apalache.infra.passes.WriteablePassOptions

import com.typesafe.scalalogging.LazyLogging
import java.io.{File, FileInputStream, PrintWriter, FileWriter}
import java.nio.file.{Files, Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import org.yaml.snakeyaml.Yaml

trait OutputManagerConfig {
  def outDir: Option[File]
  def writeIntermediate: Option[Boolean]
  def profiling: Option[Boolean]
}

/**
 * The OutputManager is the central source of truth, for all IO related locations.
 * Any IO operation should request read/write target paths from this object.
 */
object OutputManager extends LazyLogging {

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
  // This should only be set if the IntermediateFlag is true
  private var intermediateDirOpt: Option[Path] = None
  private var runDirOpt: Option[Path] = None
  private var flags: Map[String, Boolean] =
    Map(
        IntermediateFlag -> false,
        ProfilingFlag -> false
    )

  private def setOutDir(base: Path, namespace: String): Unit = {
    outDirOpt = Some(base.resolve(namespace).toAbsolutePath())
  }

  /* This should only ever be set if the IntermediateFlag is true */
  private def setIntermediateDir(namespace: String): Unit = {
    intermediateDirOpt = Some(runDir.resolve(IntermediateFoldername))
  }

  /** If this is FALSE, outputs (of any sort) cannot happen, so the tool should exit */
  def isConfigured: Boolean = outDirOpt.nonEmpty

  /** Accessor, read-only */
  def runDirPathOpt: Option[Path] = runDirOpt

  /**
   * Accessor for the configured output directory.
   *
   * @throws IllegalStateException if called before OutputManager is configured: this is considered an implementator error
   */
  def outDir: Path = {
    outDirOpt.getOrElse(throw new IllegalStateException("out-dir is not configured"))
  }

  /**
   * Accessor for the configured run directory.
   *
   * @throws IllegalStateException if called before OutputManager is configured: this is considered an implementator error
   */
  def runDir: Path = {
    runDirOpt.getOrElse(throw new IllegalStateException("run directory does not exist"))
  }

  /**
   * Accessor for the configured latest directory
   *
   * The output results from the *latest* run are always written here.
   *
   * @throws IllegalStateException if called before OutputManager is configured: this is considered an implementator error
   */
  def latestDir: Path = {
    outDir.resolve("latest")
  }

  private def latestIntermediateDir: Option[Path] = {
    if (intermediateDirOpt.isEmpty) {
      None
    } else {
      Some(latestDir.resolve(IntermediateFoldername))
    }
  }

  private def ensureDirExists(path: Path): Unit = {
    val f = path.toFile
    if (!((f.exists() && f.isDirectory()) || f.mkdirs())) {
      throw new ConfigurationError(s"Could not find or create directory: ${f.getCanonicalPath}.")
    }
  }

  private def expandedFilePath(s: String): Path = {
    val home = System.getProperty("user.home")
    Paths.get(if (s.startsWith("~")) s.replaceFirst("~", home) else s)
  }

  /** Loads the Apalache configuration file from HOME/.tlaplus */
  private def syncFromGlobalConfig(namespace: String): Unit = {
    val home = System.getProperty("user.home")
    val configFile = new File(home, CfgFile)
    if (configFile.exists()) {
      val yaml = new Yaml
      val configYaml: java.util.Map[String, Any] = yaml.load(new FileInputStream(configFile.getCanonicalPath))

      configYaml.forEach { case (flagName, flagValue) =>
        // `OutdirNameInCfg` is a special flag that governs the output directory
        if (flagName == OutdirNameInCfg) {
          flagValue match {
            case path: String => setOutDir(expandedFilePath(path), namespace)
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
      setOutDir(Paths.get(System.getProperty("user.dir"), DefaultOutdir), namespace)
    }
  }

  /** Configure OutputManager based on supported CLI flags */
  // TODO(shon): Perhaps we should reworking this object as a class that takes a configuration
  // matching the specification of this trait?
  private def syncFromCli(namespace: String, cli: OutputManagerConfig): Unit = {
    cli.outDir.foreach(d => setOutDir(d.toPath(), namespace))
    cli.writeIntermediate.foreach(flags += IntermediateFlag -> _)
    cli.profiling.foreach(flags += ProfilingFlag -> _)
  }

  /**
   * Configure OutputManager, with cli configuration taking precedence
   * over the configuration file
   */
  def configure(namespace: String, cli: OutputManagerConfig): Unit = {
    syncFromGlobalConfig(namespace)
    syncFromCli(namespace, cli)

    ensureDirExists(outDir)
    createRunDirectory()
    ensureDirExists(latestDir)
    if (flags(Names.IntermediateFlag)) {
      setIntermediateDir(namespace)
      // `get` is safe because `setIntermediateDir` ensures the intermdiate
      ensureDirExists(intermediateDirOpt.get)
      // `get` is safe because `ensureDirExists(latestDir)` has run
      ensureDirExists(latestIntermediateDir.get)
    }
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
   *  Create a PrintWriter to the file formed by appending `fileParts` to the `base` file
   *
   * E.g., to create a writer to the file `foo/bar/bas.json`:
   *
   *    val w = printWriter("foo", "bar", "baz.json")
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
  def withWriterInRunDir(parts: String*)(f: PrintWriter => Unit): Unit = {
    runDirOpt.map {
      runDir =>
      withWriter(f)(printWriter(runDir, parts: _*))
      withWriter(f)(printWriter(latestDir, parts: _*))
    }
  }

  /**
   * Conditionally applies a function to a PrintWriter constructed relative to the intermediate directory
   *
   * @param parts path parts describing a path relative to the intermediate directory (all parents must exist)
   * @param f a function that will be applied to the `PrintWriter`, if the `IntermediateFlag` is set.
   * @return `true` if the `IntermediateFlag` is true, and `f` can be applied to the PrintWriter
   *        created by appending the `parts` to the intermediate output dir. Otherwise, `false`.
   */
  def withWriterInIntermediateDir(parts: String*)(f: PrintWriter => Unit): Boolean = {
    intermediateDirOpt.flatMap(d => latestIntermediateDir.map((d, _))) match {
      case Some((runDir, latestDir)) => {
        withWriter(f)(printWriter(runDir, parts: _*))
        withWriter(f)(printWriter(latestDir, parts: _*))
        true
      }
      case None => false
    }
  }
}
