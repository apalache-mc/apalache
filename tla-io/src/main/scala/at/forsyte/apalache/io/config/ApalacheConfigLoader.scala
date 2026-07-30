package at.forsyte.apalache.io.config

import at.forsyte.apalache.io.config.Constants._

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

/**
 * Selects at most one JSON configuration file and merges it below a primary configuration.
 *
 * File selection, from highest to lowest precedence, is an explicit file from the primary configuration, a
 * `.apalache.json` in the working directory, and the user-wide `.tlaplus/apalache.json`. Parent directories are not
 * searched. Defaults are applied later by [[ApalacheConfigResolver]].
 *
 * @param currentWorkingDirectory
 *   Directory in which to look for `.apalache.json`.
 * @param userHomeDirectory
 *   JVM user home containing the user-wide configuration.
 */
final class ApalacheConfigLoader(
    currentWorkingDirectory: Path = Path.of("").toAbsolutePath.normalize(),
    userHomeDirectory: Path = Path.of(System.getProperty(USER_HOME_PROPERTY)).toAbsolutePath.normalize()) {

  import ApalacheConfigLoader._

  /** Select, decode, and merge at most one file below `primary`. */
  def load(primary: ApalacheConfig): ConfigParseResult[ApalacheConfig] = {
    selectedFile(primary) match {
      case Left(error) =>
        ConfigParseResult.failure(error)

      case Right(None) =>
        ConfigParseResult.success(primary)

      case Right(Some(selected)) =>
        val decoded = decodeFile(selected.path, selected.label)
        if (decoded.isSuccess) {
          ConfigParseResult.success(
              primary.mergeWithLower(decoded.requireValue()),
              decoded.warnings,
          )
        } else {
          ConfigParseResult.failureFrom(decoded)
        }
    }
  }

  /** Choose one file without inspecting any lower-precedence candidate after a match. */
  private def selectedFile(primary: ApalacheConfig): Either[String, Option[SelectedFile]] = {
    primary.context.configFile match {
      case Some(path) if isLegacyFilename(path) =>
        Left(legacyFilenameError(path))

      case Some(path) =>
        Right(Some(SelectedFile(path, path.toString)))

      case None =>
        val local = currentWorkingDirectory.resolve(LOCAL_CONFIG_FILENAME)
        if (Files.exists(local)) {
          Right(Some(SelectedFile(local, LOCAL_CONFIG_FILENAME)))
        } else {
          val global = userHomeDirectory.resolve(TLA_PLUS_DIRECTORY).resolve(GLOBAL_CONFIG_FILENAME)
          if (Files.exists(global)) Right(Some(SelectedFile(global, global.toString)))
          else Right(None)
        }
    }
  }

  /** Read and decode one selected file. */
  private def decodeFile(path: Path, label: String): ConfigParseResult[ApalacheConfig] = {
    if (!Files.exists(path)) {
      return ConfigParseResult.failure(s"Configuration file not found: ${path.toAbsolutePath}")
    }

    val text =
      try Files.readString(path, StandardCharsets.UTF_8)
      catch {
        case e: java.io.IOException =>
          return ConfigParseResult.failure(s"$label: Could not read configuration: ${e.getMessage}")
      }

    val decoded = ApalacheConfigJsonParser.parse(text, label)
    if (decoded.isSuccess) {
      decoded
    } else {
      ConfigParseResult.failure(
          decoded.errors.map { error =>
            if (error.startsWith(label)) error else s"$label: $error"
          },
          decoded.warnings,
      )
    }
  }
}

/** Convenience entry point using the process working and JVM user-home directories. */
object ApalacheConfigLoader {
  final private case class SelectedFile(path: Path, label: String)

  /** Select and load at most one file below `primary`. */
  def load(primary: ApalacheConfig): ConfigParseResult[ApalacheConfig] =
    new ApalacheConfigLoader().load(primary)

  /** Return whether an explicitly selected path uses the unsupported `.cfg` suffix. */
  private def isLegacyFilename(path: Path): Boolean =
    path.getFileName.toString.endsWith(LEGACY_CONFIG_EXTENSION)

  /** Explain how to replace a legacy application-configuration filename. */
  private def legacyFilenameError(path: Path): String = {
    val filename = path.getFileName.toString
    val replacement = path.resolveSibling(filename.dropRight(LEGACY_CONFIG_EXTENSION.length) + JSON_EXTENSION)
    if (Files.exists(replacement)) {
      s"Legacy Apalache configuration file $path is not supported. Remove it; use $replacement."
    } else {
      s"Legacy Apalache configuration file $path is not supported. Rename it to $replacement and convert it to strict JSON."
    }
  }
}
