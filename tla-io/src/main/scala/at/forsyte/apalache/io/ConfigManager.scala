package at.forsyte.apalache.io

import pureconfig._
import pureconfig.generic.auto._
import java.io.{File}
import java.nio.file.{Path, Files, Paths}

object Converters {

  private def expandedFilePath(s: String): Path = {
    Paths.get(if (s.startsWith("~")) s.replaceFirst("~", System.getProperty("user.home")) else s)
  }

  // Value class to allow adding a new implicit for the File
  case class ExpandedFile(val file: File) extends AnyVal

  object ExpandedFile {
    def apply(f: File): ExpandedFile = {
      new ExpandedFile(expandedFilePath(f.toString()).toFile())
    }
  }

  // Value class to allow adding a new implicit for Path
  case class ExpandedPath(val path: Path) extends AnyVal

  object ExpandedPath {
    def apply(f: Path): ExpandedPath = {
      new ExpandedPath(expandedFilePath(f.toString()))
    }
  }

  // Briniging these implicits in scope lets us override the existing
  // file deserialization behavior, so we get path expansion in all configured
  // paths
  implicit def expandedFileConfigReader: ConfigReader[ExpandedFile] =
    ConfigReader[File].map(ExpandedFile.apply)

  implicit def expandedPathConfigReader: ConfigReader[ExpandedPath] =
    ConfigReader[Path].map(ExpandedPath.apply)
}

/** The configuration values that can be overriden based on CLI arguments */
trait CliConfig {

  /** Input file */
  def file: File
  def outDir: Option[File]
  def runDir: Option[File]
  def writeIntermediate: Option[Boolean]
  def profiling: Option[Boolean]
  def configFile: Option[File]
}

/** The application's configurable values, along with their base defaults */
case class ApalacheConfig(
    file: Option[File] = None, outDir: File = new File(System.getProperty("user.dir"), "_apalache-out"),
    runDir: Option[File] = None, configFile: Option[File] = None, writeIntermediate: Boolean = false,
    profiling: Boolean = false
)

case class ConfigManager(cmd: CliConfig) {
  val TLA_PLUS_DIR = ".tlaplus"
  val APALACHE_CFG = "apalache.cfg"
  val DOT_APALACHE_CFG = "." + APALACHE_CFG

  import Converters._

  // Recursively search parents of given `dir`, looking for .apalache.cfg file
  private def findLocalConfig(dir: Path): Option[ConfigObjectSource] = {
    val localCfg = dir.resolve(DOT_APALACHE_CFG)
    if (Files.exists(localCfg)) {
      Some(ConfigSource.file(localCfg))
    } else {
      Option(dir.getParent).flatMap(findLocalConfig)
    }
  }

  private def localConfig(): Option[ConfigObjectSource] = {
    // TODO Ensure an error is raised if config file is specifid in cmd but file cannot be loaded!
    cmd.configFile.map(ConfigSource.file).orElse(findLocalConfig(Paths.get(".").toAbsolutePath()))
  }

  /**
   * Load the application configuration from all sources supported by apalache
   *
   * The following precedence is maintained, wherein lower numbered items override highest numbered items:
   *
   * 1. CLI arguments
   * 2. Environment variables (Overiding is taken care of by CLI parsing library)
   * 3. Local config file
   * 4. Globacl config file
   * 5. `ApalacheConfig` defaults (as specified in the case class definition)
   */
  def load(): ConfigReader.Result[ApalacheConfig] = {

    val home = System.getProperty("user.home")
    val globalConfig = ConfigSource.file(Paths.get(home, TLA_PLUS_DIR, APALACHE_CFG))

    localConfig
      .getOrElse(ConfigSource.empty)
      // `withFallback` supplies configuration sources that only apply if the preceding configs aren't set
      .withFallback(globalConfig.optional)
      .load[ApalacheConfig]
      .map(cfg =>
        // TODO Is there no better way than hardcoding these overrides?
        cfg.copy(
            file = Some(cmd.file),
            outDir = cmd.outDir.getOrElse(cfg.outDir),
            runDir = cmd.runDir.orElse(cfg.runDir),
            configFile = cmd.configFile.orElse(cfg.configFile),
            writeIntermediate = cmd.writeIntermediate.getOrElse(cfg.writeIntermediate),
            profiling = cmd.profiling.getOrElse(cfg.profiling)
        )
      )
  }
}

object ConfigManager {

  /** Load the application configuration, or raise a configuration error */
  def apply(cmd: CliConfig): ApalacheConfig = {
    new ConfigManager(cmd).load() match {
      case Left(err)  => throw new ConfigurationError(err.toString())
      case Right(cfg) => cfg
    }
  }
}
