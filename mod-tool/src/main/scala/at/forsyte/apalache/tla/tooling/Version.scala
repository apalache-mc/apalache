package at.forsyte.apalache.tla.tooling

import java.io.IOException
import java.util.Properties

object Version {
  private val pomProps: Properties = loadProperties("META-INF/maven/at.forsyte.apalache/tool/pom.properties")
  private val gitProps: Properties = loadProperties("at/forsyte/apalache/tla/tooling/git.properties")

  def version: String = {
    pomProps.getProperty("version", "version-dev")
  }

  def build: String = {
    gitProps.getProperty("git.commit.id.describe", "unknown-build")
  }

  private def loadProperties(name: String): Properties = {
    val resourceStream = ClassLoader.getSystemClassLoader.getResourceAsStream(name)
    var props = new Properties()
    try {
      if (resourceStream != null) {
        props.load(resourceStream)
      }
    } catch {
      case _: IOException => ()
        // ignore and set defaults, this is not a critical function

      case e: Throwable => throw e
    }

    props
  }
}
