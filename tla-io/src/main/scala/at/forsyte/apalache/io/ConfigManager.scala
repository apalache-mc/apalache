package at.forsyte.apalache.io

import pureconfig._
import pureconfig.generic.auto._
import pureconfig.generic.ProductHint
import java.io.File
import java.nio.file.{Files, Path, Paths}
import at.forsyte.apalache.tla.lir.Feature
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import com.typesafe.config.{Config, ConfigObject}
import scala.util.Try

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

  // Do not allow unknown keys
  // See https://pureconfig.github.io/docs/overriding-behavior-for-case-classes.html#unknown-keys
  implicit val hint = ProductHint[ApalacheConfig](allowUnknownKeys = false)
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
   * Load the application configuration from all sources supported by apalache, and merge with the primary `cfg`
   *
   * The following precedence is maintained, wherein configured values found from lower numbered sources override values
   * from higher numbered sources:
   *
   *   1. The primary `cfg` supplied as a parameter (typically derived from the CLI)
   *   1. Local config file
   *   1. Global config file
   *   1. `ApalacheConfig` defaults (as specified in the case class definition)
   *
   * @param cfg
   *   The primary configuration, which will be used to override values from other configs.
   */
  def load(cfg: ApalacheConfig): ConfigReader.Result[ApalacheConfig] = {

    val home = System.getProperty("user.home")
    val globalConfig = ConfigSource.file(Paths.get(home, TLA_PLUS_DIR, APALACHE_CFG))

    val localConfig: ConfigObjectSource =
      cfg.common.configFile.orElse(findLocalConfig(Paths.get(".").toAbsolutePath())) match {
        case Some(cfgFile) => ConfigSource.file(cfgFile)
        case None          => ConfigSource.empty
      }

    // Derive lightbend `Config` objects from the default and primary config
    // case classes.
    //
    // The cast to `ConfigObject` is guaranteed to be safe: `ConfigWriter.to`
    // produces a `ConfigValue`, of which `ConfigObject` is a subtype
    // representing values that are dictionaries. Case classes are always
    // represented as dictionaries, so we can be sure any `ConfigValue` derived
    // from an instance of an `ApalacheConfig` can be cast `asInstanceOf[ConfigObject]`.
    val defaults: Config =
      ConfigWriter[ApalacheConfig].to(ApalacheConfig()).asInstanceOf[ConfigObject].toConfig()
    val primaryConfig: Config = ConfigWriter[ApalacheConfig].to(cfg).asInstanceOf[ConfigObject].toConfig()

    ConfigSource
      .fromConfig(primaryConfig)
      // `withFallback` supplies configuration sources that only apply if values in the preceding configs aren't set
      .withFallback(localConfig)
      .withFallback(globalConfig.optional) // "optional" entails this will be empty if the file is absent
      .withFallback(ConfigSource.fromConfig(defaults))
      .load[ApalacheConfig]
  }
}

object ConfigManager {

  /** Load the application configuration, converting any configuration error into a pretty printed message */
  def apply(cfg: ApalacheConfig): Try[ApalacheConfig] =
    new ConfigManager().load(cfg).left.map(err => new ConfigurationError(err.prettyPrint())).toTry

}
