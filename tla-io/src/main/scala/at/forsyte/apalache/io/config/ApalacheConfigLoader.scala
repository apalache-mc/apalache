package at.forsyte.apalache.io.config

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import scala.collection.mutable.ListBuffer

/**
 * Discovers local and user-wide JSON configuration files and merges them below a primary configuration.
 *
 * Precedence, from highest to lowest, is primary/CLI, local, global. Defaults are applied later by
 * `ApalacheConfigResolver`.
 *
 * @param workingDirectory
 *   Starting directory for local configuration discovery.
 * @param homeDirectory
 *   Home directory containing the user-wide configuration.
 */
final class ApalacheConfigLoader(
    workingDirectory: Path = Paths.get("").toAbsolutePath.normalize(),
    homeDirectory: Path = Paths.get(System.getProperty("user.home"))) {

  import ApalacheConfigLoader._

  /**
   * Discover, decode, and merge configuration files below the primary configuration.
   *
   * @param primary
   *   Highest-precedence configuration, normally produced by the CLI or RPC boundary.
   * @return
   *   The merged sparse configuration and warnings, or all loading and decoding errors found.
   */
  def loadWithFallbacks(primary: ApalacheConfig): ConfigParseResult[ApalacheConfig] = {
    val errors = ListBuffer.empty[String]
    val warnings = ListBuffer.empty[String]
    val configurations = ListBuffer.empty[ApalacheConfig]

    discoverGlobal().foreach { discovered =>
      errors ++= discovered.errors
      discovered.path.foreach { path =>
        addDecodedFile(path, discovered.label, errors, warnings, configurations)
      }
    }

    primary.context.configFile match {
      case Some(path) =>
        if (isLegacyFilename(path)) {
          errors += legacyFilenameError(path)
        } else {
          addDecodedFile(path, path.toString, errors, warnings, configurations)
        }

      case None =>
        val discovered = discoverLocal(workingDirectory)
        errors ++= discovered.errors
        discovered.path.foreach { path =>
          addDecodedFile(path, discovered.label, errors, warnings, configurations)
        }
    }

    if (errors.nonEmpty) {
      ConfigParseResult.failure(errors.toList, warnings.toList)
    } else {
      var merged = ApalacheConfig.empty
      configurations.foreach { config =>
        merged = config.mergeWithLower(merged)
      }
      merged = primary.mergeWithLower(merged)
      ConfigParseResult.success(merged, warnings.toList)
    }
  }

  /** Read and decode one file, appending either its configuration or its diagnostics to the supplied accumulators. */
  private def addDecodedFile(
      path: Path,
      label: String,
      errors: ListBuffer[String],
      warnings: ListBuffer[String],
      configurations: ListBuffer[ApalacheConfig]): Unit = {

    if (!Files.exists(path)) {
      errors += s"Configuration file not found: ${path.toAbsolutePath}"
      return
    }

    val text =
      try Files.readString(path, StandardCharsets.UTF_8)
      catch {
        case e: java.io.IOException =>
          errors += s"$label: Could not read configuration: ${e.getMessage}"
          return
      }

    val decoded = ApalacheConfigJsonParser.parse(text, label)
    warnings ++= decoded.warnings
    if (decoded.isSuccess) {
      configurations += decoded.requireValue()
    } else {
      decoded.errors.foreach { error =>
        if (error.startsWith(label)) errors += error
        else errors += s"$label: $error"
      }
    }
  }

  /** Search the starting directory and its parents, reporting any legacy application config as an error. */
  private def discoverLocal(start: Path): Discovered = {
    var current: Path = start
    while (current != null) {
      val json = current.resolve(LocalJson)
      val legacy = current.resolve(LocalLegacy)
      if (Files.exists(json)) {
        val errors =
          if (Files.exists(legacy)) {
            List(legacyFilenameError(legacy))
          } else {
            Nil
          }
        return Discovered(Some(json), start.relativize(json).toString, errors)
      }
      if (Files.exists(legacy)) {
        return Discovered(
            None,
            "",
            List(legacyFilenameError(legacy)),
        )
      }
      current = current.getParent
    }
    Discovered.none
  }

  /** Discover the user-wide configuration, reporting a legacy application config as an error. */
  private def discoverGlobal(): Option[Discovered] = {
    val directory = homeDirectory.resolve(TlaPlusDirectory)
    val json = directory.resolve(GlobalJson)
    val legacy = directory.resolve(GlobalLegacy)
    if (Files.exists(json)) {
      val errors =
        if (Files.exists(legacy)) {
          List(legacyFilenameError(legacy))
        } else {
          Nil
        }
      Some(Discovered(Some(json), json.toString, errors))
    } else if (Files.exists(legacy)) {
      Some(Discovered(
              None,
              "",
              List(legacyFilenameError(legacy)),
          ))
    } else {
      None
    }
  }
}

/** Convenience entry points using the process working and home directories. */
object ApalacheConfigLoader {
  private val TlaPlusDirectory = ".tlaplus"
  private val LocalJson = ".apalache.json"
  private val LocalLegacy = ".apalache.cfg"
  private val GlobalJson = "apalache.json"
  private val GlobalLegacy = "apalache.cfg"

  /** A discovered configuration path together with its diagnostic label and discovery errors. */
  final private case class Discovered(path: Option[Path], label: String, errors: List[String])
  private object Discovered {
    val none: Discovered = Discovered(None, "", Nil)
  }

  /**
   * Load file-based fallbacks and merge them below a primary configuration.
   *
   * @param primary
   *   Highest-precedence configuration, normally produced by the CLI.
   * @return
   *   The merged sparse configuration, or loading and decoding errors.
   */
  def loadWithFallbacks(primary: ApalacheConfig): ConfigParseResult[ApalacheConfig] =
    new ApalacheConfigLoader().loadWithFallbacks(primary)

  /**
   * Decode primary JSON and merge local and user-wide fallbacks below it.
   *
   * @param json
   *   Strict JSON containing the highest-precedence configuration.
   * @return
   *   The merged sparse configuration, or decoding and loading errors.
   */
  def loadJsonWithFallbacks(json: String): ConfigParseResult[ApalacheConfig] = {
    val decoded = ApalacheConfigJsonParser.parse(json, "<configuration>")
    if (!decoded.isSuccess) {
      ConfigParseResult.failureFrom(decoded)
    } else {
      ConfigParseResult.withWarnings(
          new ApalacheConfigLoader().loadWithFallbacks(decoded.requireValue()),
          decoded.warnings,
      )
    }
  }

  /** Return whether a path uses the unsupported `.cfg` suffix. */
  private def isLegacyFilename(path: Path): Boolean =
    path.getFileName.toString.endsWith(".cfg")

  /** Explain how to replace a legacy application-configuration filename. */
  private def legacyFilenameError(path: Path): String = {
    val filename = path.getFileName.toString
    val replacement = path.resolveSibling(filename.dropRight(".cfg".length) + ".json")
    if (Files.exists(replacement)) {
      s"Legacy Apalache configuration file $path is not supported. Remove it; use $replacement."
    } else {
      s"Legacy Apalache configuration file $path is not supported. Rename it to $replacement and convert it to strict JSON."
    }
  }
}
