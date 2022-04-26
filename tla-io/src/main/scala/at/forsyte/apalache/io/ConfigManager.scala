package at.forsyte.apalache.io

import pureconfig._
import pureconfig.generic.auto._
import java.io.File
import java.nio.file.{Files, Path, Paths}
import at.forsyte.apalache.tla.lir.Feature

// Provides implicit conversions used when deserializing into configurable values.
private object Converters {
  import pureconfig.ConvertHelpers._

  private def expandedFilePath(s: String): Path = {
    Paths.get(if (s.startsWith("~")) s.replaceFirst("~", System.getProperty("user.home")) else s)
  }

  // Bringing these implicits in scope lets us override the existing File and
  // Path deserialization behavior, so we get path expansion in all configured
  // paths.
  // See https://pureconfig.github.io/docs/overriding-behavior-for-types.html
  implicit val overridePathReader = ConfigReader.fromString[Path](catchReadError(expandedFilePath))
  implicit val overrideFileReader = ConfigReader.fromString[File](catchReadError(expandedFilePath(_).toFile()))
  // PureConfig's optF will convert None values to appropriate configuration errors
  implicit val featureReader = ConfigReader.fromString[Feature](optF(Feature.fromString))
}

/**
 * The configuration values that can be overriden based on CLI arguments
 *
 * For documentation on the use and meaning of these fields, see [[at.forsyte.apalache.tla.tooling.opt.General]].
 */
trait CliConfig {

  /** Input file */
  def file: File
  def outDir: Option[File]
  def runDir: Option[File]
  def writeIntermediate: Option[Boolean]
  def profiling: Option[Boolean]
  def configFile: Option[File]
  def features: Seq[Feature]
}

/** The application's configurable values, along with their base defaults */
case class ApalacheConfig(
    file: Option[File] = None,
    outDir: File = new File(System.getProperty("user.dir"), "_apalache-out"),
    runDir: Option[File] = None,
    configFile: Option[File] = None,
    writeIntermediate: Boolean = false,
    profiling: Boolean = false,
    features: Seq[Feature] = Seq())

case class ConfigManager(cmd: CliConfig) {
  private val TLA_PLUS_DIR = ".tlaplus"
  private val APALACHE_CFG = "apalache.cfg"
  private val DOT_APALACHE_CFG = "." + APALACHE_CFG

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
    cmd.configFile.map(ConfigSource.file).orElse(findLocalConfig(Paths.get(".").toAbsolutePath()))
  }

  /**
   * Load the application configuration from all sources supported by apalache
   *
   * The following precedence is maintained, wherein lower numbered items override highest numbered items:
   *
   *   1. CLI arguments 2. Environment variables (Overiding is taken care of by CLI parsing library) 3. Local config
   *      file 4. Globacl config file 5. `ApalacheConfig` defaults (as specified in the case class definition)
   */
  def load(): ConfigReader.Result[ApalacheConfig] = {

    val home = System.getProperty("user.home")
    val globalConfig = ConfigSource.file(Paths.get(home, TLA_PLUS_DIR, APALACHE_CFG))

    localConfig()
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
            profiling = cmd.profiling.getOrElse(cfg.profiling),
            features = if (cmd.features.nonEmpty) cmd.features else cfg.features,
        ))
  }
}

object ConfigManager {

  /** Load the application configuration, converting any configuration error into a pretty printed message */
  def apply(cmd: CliConfig): Either[String, ApalacheConfig] =
    new ConfigManager(cmd).load().left.map(_.prettyPrint())
}
