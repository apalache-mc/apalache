package at.forsyte.apalache.io

import pureconfig._
import pureconfig.generic.auto._
import java.io.File
import java.nio.file.{Files, Path, Paths}
import at.forsyte.apalache.infra.passes.options.Config.ApalacheConfig
import at.forsyte.apalache.infra.passes.options.Converters

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

    val defaults: ConfigObjectSource = ApalacheConfig().toConfigSource()
    val primaryConfig: ConfigObjectSource = cfg.toConfigSource()

    // `withFallback` supplies configuration sources that only apply if values in the preceding configs aren't set
    primaryConfig
      .withFallback(localConfig)
      .withFallback(globalConfig.optional) // "optional" entails this will be empty if the file is absent
      .withFallback(defaults)
      .load[ApalacheConfig]
  }
}

object ConfigManager {

  /** Load the application configuration, converting any configuration error into a pretty printed message */
  def apply(cfg: ApalacheConfig): Either[String, ApalacheConfig] =
    new ConfigManager().load(cfg).left.map(_.prettyPrint())

}
