import pureconfig._
import pureconfig.generic.auto._
import java.io.{File}
import java.nio.file.{Path, Files, Paths}

/** The configuration values that can be overriden based on CLI arguments */
trait CliConfig {
  def outDir: Option[File]
  def runDir: Option[File]
  def writeIntermediate: Option[Boolean]
  def profiling: Option[Boolean]
  def configFile: Option[File]
}

/** The applications configurable values, along with their base defaults */
case class ApalacheConfigs(
    outDir: Option[File] = None, runDir: Option[File] = None, configFile: Option[File] = None,
    writeIntermediate: Boolean = false, profiling: Boolean = false
)

case class ConfigManager(cmd: CliConfig) {
  val TLA_PLUS_DIR = ".tlaplus"
  val APALACHE_CFG = "aplache.cfg"
  val DOT_APALACHE_CFG = "." + APALACHE_CFG

  // Recursively search parents of given, looking for .apalache.cfg file
  private def findLocalConfig(dir: Path): Option[ConfigObjectSource] = {
    val localCfg = dir.resolve(DOT_APALACHE_CFG)
    if (Files.exists(localCfg)) {
      Some(ConfigSource.file(localCfg))
    } else {
      findLocalConfig(dir.getParent)
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
   * 1. CLI arguments
   * 2. Environment variables (Overiding is taken care of by CLI parsing library)
   * 3. Local config file
   * 4. Globacl config file
   * 5. `ApalacheConfig` defaults (as specified in the case class definition)
   */
  def load(): ConfigReader.Result[ApalacheConfigs] = {
    val home = System.getProperty("user.home")
    val globalConfig = ConfigSource.file(Paths.get(home, TLA_PLUS_DIR, APALACHE_CFG))
    localConfig
      .getOrElse(ConfigSource.empty)
      .optional
      // `withFallback` supplies configuration sources that only apply if the preceding configs aren't set
      .withFallback(globalConfig.optional)
      .load[ApalacheConfigs]
      .map(cfg =>
        // TODO Is there no better way than hardcoding these overrides?
        cfg.copy(
            outDir = cmd.outDir.orElse(cfg.outDir),
            runDir = cmd.runDir.orElse(cfg.runDir),
            configFile = cmd.configFile.orElse(cfg.configFile),
            writeIntermediate = cmd.writeIntermediate.getOrElse(cfg.writeIntermediate),
            profiling = cmd.profiling.getOrElse(cfg.profiling)
        )
      )
  }
}
