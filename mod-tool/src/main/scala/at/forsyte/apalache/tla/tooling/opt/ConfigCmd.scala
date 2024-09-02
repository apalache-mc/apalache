package at.forsyte.apalache.tla.tooling.opt

import org.backuity.clist.opt
import java.io.File
import com.typesafe.scalalogging.LazyLogging

// imports from Sany utils
import util.ExecutionStatisticsCollector
import util.ExecutionStatisticsCollector.Selection
import at.forsyte.apalache.infra.ExitCodes

/**
 * This command initiates the 'config' command line.
 *
 * @author
 *   Igor Konnov
 */
class ConfigCmd extends ApalacheCommand(name = "config", description = "Configure Apalache options") with LazyLogging {

  var submitStats: Option[Boolean] = opt[Option[Boolean]](name = "enable-stats",
      description = "Let Apalache submit usage statistics to tlapl.us\n"
        + "(shared with TLC and TLA+ Toolbox)\nSee: https://apalache-mc.org/docs/apalache/statistics.html")

  def run() = {
    logger.info("Configuring Apalache")

    if (!configDirExistsOrCreated()) {
      logger.warn("Unable to update statistics configuration. The other features will keep working.")
      Left(ExitCodes.ERROR, "Configuration directory could not be found or created")
    } else {
      submitStats.foreach { isEnabled =>
        val statCollector = new ExecutionStatisticsCollector()
        // protect against potential exceptions in the tla2tools code
        if (isEnabled) {
          statCollector.set(Selection.ON)
          logger.info("Statistics collection is ON.")
          logger.info("This also enabled TLC and TLA+ Toolbox statistics.")
        } else {
          statCollector.set(Selection.NO_ESC)
          logger.info("Statistics collection is OFF.")
          logger.info("This also disabled TLC and TLA+ Toolbox statistics.")
        }
      }
      Right("Configuration complete")
    }
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
