package at.forsyte.apalache.io

import pureconfig._
import pureconfig.generic.auto._
import pureconfig.generic.semiauto._
import pureconfig.generic.ProductHint
import pureconfig.generic.FieldCoproductHint
import java.io.File
import java.nio.file.{Files, Path, Paths}
import at.forsyte.apalache.tla.lir.Feature
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import com.typesafe.config.{Config, ConfigObject}
import scala.util.Try
import java.io.PrintWriter
import com.typesafe.config.ConfigRenderOptions
import at.forsyte.apalache.infra.passes.options.SourceOption
import at.forsyte.apalache.infra.passes.options.Algorithm

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
  implicit val overridePathReader: ConfigReader[Path] = ConfigReader.fromString[Path](catchReadError(expandedFilePath))
  implicit val overrideFileReader: ConfigReader[File] =
    ConfigReader.fromString[File](catchReadError(expandedFilePath(_).toFile()))
  // PureConfig's optF will convert None values to appropriate configuration errors
  implicit val featureReader: ConfigReader[Feature] = ConfigReader.fromString[Feature](optF(Feature.fromString))
  implicit val featureWriter: ConfigWriter[Feature] = ConfigWriter.toString[Feature](_.toString)

  // Converstion for options.Algorithm, manual conversion here allows
  // configuration as `algo = incremental` instead of `algo = type.incremental`
  implicit val algorithmReader: ConfigReader[Algorithm] =
    ConfigReader.fromString[Algorithm](catchReadError(Algorithm.ofString))
  implicit val algorithmWriter: ConfigWriter[Algorithm] = ConfigWriter.toString[Algorithm](_.toString)

  // Derive a reader and writer for SourceOption.Format based on the case object family
  // See https://pureconfig.github.io/docs/overriding-behavior-for-sealed-families.html#sealed-families
  implicit val sourceOptionFormatReader: ConfigReader[SourceOption.Format] =
    deriveEnumerationReader[SourceOption.Format]
  implicit val sourceOptionFormatWriter: ConfigWriter[SourceOption.Format] =
    deriveEnumerationWriter[SourceOption.Format]

  // Do not allow unknown keys
  // See https://pureconfig.github.io/docs/overriding-behavior-for-case-classes.html#unknown-keys
  implicit val hint: ProductHint[ApalacheConfig] = ProductHint[ApalacheConfig](allowUnknownKeys = false)

  // Enables encoding and decoding `SourceOption`s on the base the value of a `type` field
  // See https://pureconfig.github.io/docs/overriding-behavior-for-sealed-families.html#sealed-families
  implicit val sourceOptionHint: FieldCoproductHint[SourceOption] = new FieldCoproductHint[SourceOption]("type") {
    // Truncates the required value of `type` so that only `file` or `string` is needed, instead of requiring `fileSource` or `stringSource`
    // E.g.:
    //
    //   source {
    //       file="test/tla/Counter.tla"
    //       format=tla
    //       type=file
    //   }
    override def fieldValue(name: String) = name.dropRight("Source".length).toLowerCase()
  }
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

  import Converters._

  /** Load the application configuration, converting any configuration error into a pretty printed message */
  def apply(cfg: ApalacheConfig): Try[ApalacheConfig] =
    new ConfigManager().load(cfg).left.map(err => new ConfigurationError(err.prettyPrint())).toTry

  /** Load a config from a string encoding */
  def apply(string: String): Try[ApalacheConfig] = {
    ConfigSource
      .string(string)
      .load[ApalacheConfig]
      .left
      .map(err => new ConfigurationError(err.prettyPrint()))
      .toTry
      .flatMap(apply(_))
  }

  /** Save the given `cfg` into the `dst` `PrintWriter` */
  def save(cfg: ApalacheConfig)(dst: PrintWriter): Unit = {
    val cfgString = ConfigWriter[ApalacheConfig].to(cfg).asInstanceOf[ConfigObject].render(renderOptions)
    dst.print(cfgString)
  }

  /** Render the given `cfg` as a JSON string */
  def serialize(cfg: ApalacheConfig): String = {
    ConfigWriter[ApalacheConfig].to(cfg).asInstanceOf[ConfigObject].render(ConfigRenderOptions.concise())
  }

  // Configure the rendering options for dumping the configuration
  private val renderOptions: ConfigRenderOptions = {
    ConfigRenderOptions
      .concise()
      // Preserve comments from loaded configurations (tho not generally possible for our current system)
      .setComments(true)
      // Format the output
      .setFormatted(true)
      // Use the cleaner HOCON syntax instead of JSON
      .setJson(false)
  }
}
