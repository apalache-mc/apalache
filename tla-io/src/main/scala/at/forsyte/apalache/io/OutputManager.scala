package at.forsyte.apalache.io

import at.forsyte.apalache.infra.passes.PassOptions

import java.io.{File, FileInputStream}
import java.nio.file.{Files, Path, Paths}
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import org.yaml.snakeyaml.Yaml

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
  // Absolute path
  private var outputDirPath: String = ""
  private var runDirOpt: Option[Path] = None
  private var flags: Map[String, Boolean] =
    Map(
        IntermediateFlag -> false,
        ProfilingFlag -> false
    )

  /** If this is FALSE, outputs (of any sort) cannot happen, so the tool should exit */
  def isConfigured: Boolean = new File(outputDirPath).isDirectory

  /** Accessor, read-only */
  def runDirPathOpt: Option[Path] = runDirOpt

  /** Loads the Apalache configuration file from HOME/.tlaplus */
  def syncFromGlobalConfig(): Unit = {
    val home = System.getProperty("user.home")
    val configFile = new File(home, CfgFile)
    if (configFile.exists()) {
      val yaml = new Yaml
      val configYaml: java.util.Map[String, Any] = yaml.load(new FileInputStream(configFile.getCanonicalPath))

      configYaml.forEach { case (flagName, flagValue) =>
        if (flagName == OutdirNameInCfg) {
          flagValue match {
            case flagValAsString: String =>
              // `OutdirNameInCfg` is a special flag that governs the output directory
              val replacedHome =
                if (flagValAsString.startsWith("~")) flagValAsString.replaceFirst("~", home)
                else flagValAsString
              val outdir = new File(replacedHome)
              // Try to make the dir, if it fails we skip and go to the default
              if (!outdir.exists()) {
                outdir.mkdir()
              }
              if (!outdir.exists()) {
                throw new ConfigurationError(s"Could not find or create directory: ${outdir.getCanonicalPath}.")
              } else {
                outputDirPath = outdir.getCanonicalPath
              }
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
    if (outputDirPath.isEmpty) {
      outputDirPath = Paths.get(System.getProperty("user.dir"), DefaultOutdir).toString
    }
  }

  // Flags can be passed from options too, e.g. --profile or --write-intermediate
  // TODO: remove this once all flag operations are moved into PassOptions
  def syncFromOptions(opt: PassOptions): Unit = {
    opt.get[Boolean]("general", IntermediateFlag) foreach {
      flags += IntermediateFlag -> _
    }
    opt.get[Boolean]("general", ProfilingFlag) foreach {
      flags += ProfilingFlag -> _
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

  /** Inside `outputDirPath`, create a directory for an individual run */
  def createRunDirectory(specName: String): Unit =
    if (runDirOpt.isEmpty) {
      val nicedate = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"yyyy-MM-dd"))
      val nicetime = LocalDateTime.now().format(DateTimeFormatter.ofPattern(s"HH-mm-ss"))
      val outdir = new File(outputDirPath)
      if (!outdir.exists()) {
        outdir.mkdir()
      }
      // prefix for disambiguation
      val rundir = Files.createTempDirectory(Paths.get(outdir.getAbsolutePath), s"${specName}_${nicedate}T${nicetime}_")
      runDirOpt = Some(rundir)
    }
}
