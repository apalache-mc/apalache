package at.forsyte.apalache.io

import pureconfig._
import pureconfig.generic.auto._
import java.io.File
import java.nio.file.{Files, Path, Paths}
import at.forsyte.apalache.tla.lir.Feature
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import com.typesafe.config.{Config, ConfigObject}

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
  implicit val featureWriter = ConfigWriter.toString[Feature](_.toString)

}

/**
 * The configuration values that can be overriden based on CLI arguments
 *
 * For documentation on the use and meaning of these fields as CLI paramter, see
 * `at.forsyte.apalache.tla.tooling.opt.General`.
 */
// TODO rm
trait CliConfig {

  /** Input file */
  def file: File
  def outDir: Option[File]
  def runDir: Option[File]
  def debug: Option[Boolean]
  def writeIntermediate: Option[Boolean]
  def profiling: Option[Boolean]
  def configFile: Option[File]
  def features: Seq[Feature]
}

/**
 * Manage cascade loading program configurations from the supported sources
 *
 * @param cmd
 *   The configurations supplied via CLI
 */
class ConfigManager() {
  private val TLA_PLUS_DIR = ".tlaplus"
  private val APALACHE_CFG = "apalache.cfg"
  private val DOT_APALACHE_CFG = "." + APALACHE_CFG

  import Converters._

  // Recursively search parents of given `dir`, looking for .apalache.cfg file
  private def findLocalConfig(dir: Path): Option[File] = {
    val localCfg = dir.resolve(DOT_APALACHE_CFG)
    if (Files.exists(localCfg)) {
      Some(localCfg.toFile())
    } else {
      Option(dir.getParent).flatMap(findLocalConfig)
    }
  }

  /**
   * Load the application configuration from all sources supported by apalache
   *
   * The following precedence is maintained, wherein configured values found from lower numbered sources override values
   * from higher numbered sources:
   *
   *   1. CLI arguments
   *   1. Environment variables (Overiding is taken care of by the CLI parsing library)
   *   1. Local config file
   *   1. Global config file
   *   1. `ApalacheConfig` defaults (as specified in the case class definition)
   */
  // TODO: remove once loading from `CliConfiguration` is fully integrated
  def load(cmd: CliConfig): ConfigReader.Result[ApalacheConfig] = {

    val home = System.getProperty("user.home")
    val globalConfig = ConfigSource.file(Paths.get(home, TLA_PLUS_DIR, APALACHE_CFG))

    val localConfig: ConfigObjectSource =
      cmd.configFile.orElse(findLocalConfig(Paths.get(".").toAbsolutePath())) match {
        case Some(cfgFile) => ConfigSource.file(cfgFile)
        case None          => ConfigSource.empty
      }

    localConfig
      // `withFallback` supplies configuration sources that only apply if the preceding configs aren't set
      .withFallback(globalConfig.optional)
      .load[ApalacheConfig]
      .map(cfg =>
        // TODO Is there no better way than hardcoding these overrides?
        cfg.copy(common = cfg.common.copy(
            file = Some(cmd.file),
            outDir = cmd.outDir.orElse(cfg.common.outDir),
            runDir = cmd.runDir.orElse(cfg.common.runDir),
            debug = cmd.debug.orElse(cfg.common.debug),
            configFile = cmd.configFile.orElse(cfg.common.configFile),
            writeIntermediate = cmd.writeIntermediate.orElse(cfg.common.writeIntermediate),
            profiling = cmd.profiling.orElse(cfg.common.profiling),
            features = if (cmd.features.nonEmpty) cmd.features else cfg.common.features,
        )))
  }

  def load(cfg: ApalacheConfig): ConfigReader.Result[ApalacheConfig] = {

    val home = System.getProperty("user.home")
    val globalConfig = ConfigSource.file(Paths.get(home, TLA_PLUS_DIR, APALACHE_CFG))

    val localConfig: ConfigObjectSource =
      cfg.common.configFile.orElse(findLocalConfig(Paths.get(".").toAbsolutePath())) match {
        case Some(cfgFile) => ConfigSource.file(cfgFile)
        case None          => ConfigSource.empty
      }

    val defaults: Config =
      ConfigWriter[ApalacheConfig].to(ApalacheConfig.default).asInstanceOf[ConfigObject].toConfig()
    val cliConfig: Config = ConfigWriter[ApalacheConfig].to(cfg).asInstanceOf[ConfigObject].toConfig()

    ConfigSource
      .fromConfig(cliConfig)
      // `withFallback` supplies configuration sources that only apply if values in the preceding configs aren't set
      .withFallback(localConfig)
      .withFallback(globalConfig.optional)
      .withFallback(ConfigSource.fromConfig(defaults))
      .load[ApalacheConfig]
  }
}

object ConfigManager {

  /** Load the application configuration, converting any configuration error into a pretty printed message */
  def apply(cmd: CliConfig): Either[String, ApalacheConfig] =
    new ConfigManager().load(cmd).left.map(_.prettyPrint())

  def apply(cfg: ApalacheConfig): Either[String, ApalacheConfig] =
    new ConfigManager().load(cfg).left.map(_.prettyPrint())

}
