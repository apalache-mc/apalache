package at.forsyte.apalache.tla.tooling

import java.io.IOException
import java.util.Properties

object Version {
  private val propertiesName = "META-INF/maven/at.forsyte.apalache/tool/pom.properties"
  private val properties: Properties = loadProperties()

  def version: String = {
    properties.getProperty("version", "version-dev")
  }

  private def loadProperties(): Properties = {
    val resourceStream = ClassLoader.getSystemClassLoader.getResourceAsStream(propertiesName)
    var props = new Properties()
    try {
      if (resourceStream != null) {
        props.load(resourceStream)
      }
    } catch {
      case _: IOException => ()
        // ignore and set defaults, this is not a critical function

      case e: Throwable => throw e
    } finally {
      if (props.isEmpty) {
        props.setProperty("version", "version-dev")
        props.setProperty("groupId", "at.forsyte.apalache")
        props.setProperty("artifactId", "tool")
      }
    }

    props
  }
}
