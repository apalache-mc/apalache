package at.forsyte.apalache.tla.tooling.opt

// imports from Sany utils
import util.ExecutionStatisticsCollector
import util.ExecutionStatisticsCollector.Selection

// clist also has a `util`, so this import must be after the Sany imports
import org.backuity.clist.{Command, _}
import java.io.File
import com.typesafe.scalalogging.LazyLogging

/**
 * This command initiates the 'config' command line.
 *
 * @author
 *   Igor Konnov
 */
class ConfigCmd
    extends Command(name = "config", description = "Configure Apalache options") with General with LazyLogging {

  var submitStats: Option[Boolean] = opt[Option[Boolean]](name = "enable-stats",
      description = "Let Apalache submit usage statistics to tlapl.us\n"
        + "(shared with TLC and TLA+ Toolbox)\nSee: https://apalache.informal.systems/docs/apalache/statistics.html")

  // Used for application (esp. output) configuration
  def file = new File("config")

  def run() = {
    logger.info("Configuring Apalache")
    submitStats.foreach { isEnabled =>
      val warning = "Unable to update statistics configuration. The other features will keep working."

      if (!configDirExistsOrCreated()) {
        logger.warn(warning)
      } else {
        val statCollector = new ExecutionStatisticsCollector()
        // protect against potential exceptions in the tla2tools code
        try {
          if (isEnabled) {
            statCollector.set(Selection.ON)
            logger.info("Statistics collection is ON.")
            logger.info("This also enabled TLC and TLA+ Toolbox statistics.")
          } else {
            statCollector.set(Selection.NO_ESC)
            logger.info("Statistics collection is OFF.")
            logger.info("This also disabled TLC and TLA+ Toolbox statistics.")
          }
        } catch {
          case e: Exception =>
            logger.warn(e.getMessage)
            logger.warn(warning)
        }
      }
    }
    Right("Configuration complete")
  }

  private def configDirExistsOrCreated(): Boolean = {
    // A temporary fix for the issue #762: create ~/.tlaplus if it does not exist
    val configDir = new File(System.getProperty("user.home", ""), ".tlaplus")
    if (configDir.exists()) {
      true
    } else {
      try {
        configDir.mkdir()
        true
      } catch {
        case e: Exception =>
          logger.warn(e.getMessage)
          logger.warn(s"Unable to create the directory $configDir.")
          false
      }
    }
  }
}
