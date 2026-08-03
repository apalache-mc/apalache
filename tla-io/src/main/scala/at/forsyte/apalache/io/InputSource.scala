package at.forsyte.apalache.io

import at.forsyte.apalache.io.config.ConfigParseResult

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

/**
 * An input source that can report its availability and read its UTF-8 content. Normally, it is a specification file or
 * a string that contains the specification (in TLA+, Quint, or JSON IR). Additionally, it can also be an ITF trace in
 * JSON.
 */
sealed abstract class InputSource {
  def format: InputSource.Format

  /** Return whether this source is available for reading. */
  def exists: Boolean

  /** Read this source as UTF-8, returning an actionable error on failure. */
  def readUtf8: ConfigParseResult[String]
}

object InputSource {

  /** Supported formats for specification and trace sources. */
  sealed abstract class Format(val name: String) {
    final override def toString: String = name
  }

  object Format {
    case object Tla extends Format("tla")
    case object Json extends Format("json")
    case object Itf extends Format("itf")
    case object Qnt extends Format("qnt")

    def fromString(value: String): Format =
      value.toLowerCase match {
        case "tla"  => Tla
        case "json" => Json
        case "itf"  => Itf
        case "qnt"  => Qnt
        case other  => throw new IllegalArgumentException(s"Unsupported source format: $other")
      }
  }

  /** A source read from a filesystem path with a known format. */
  final case class FileSource(path: Path, format: Format) extends InputSource {
    override def exists: Boolean = Files.exists(path)

    override def readUtf8: ConfigParseResult[String] =
      try {
        if (!exists) {
          ConfigParseResult.failure(s"File not found: $path")
        } else {
          ConfigParseResult.success(Files.readString(path, StandardCharsets.UTF_8))
        }
      } catch {
        case e: java.io.IOException =>
          ConfigParseResult.failure(s"Could not read $this: ${e.getMessage}")
      }

    override def toString: String = path.toString
  }

  object FileSource {
    def apply(path: Path): ConfigParseResult[FileSource] = {
      val filename = path.getFileName.toString
      val lower = filename.toLowerCase
      val format =
        if (lower.endsWith(".itf.json")) {
          Some(Format.Itf)
        } else if (lower.endsWith(".qnt.json")) {
          Some(Format.Qnt)
        } else if (lower.endsWith(".json")) {
          Some(Format.Json)
        } else if (lower.endsWith(".tla")) {
          Some(Format.Tla)
        } else {
          None
        }

      format match {
        case Some(value) => ConfigParseResult.success(FileSource(path, value))
        case None        =>
          val extension = {
            val dot = filename.lastIndexOf('.')
            if (dot >= 0) filename.substring(dot + 1) else ""
          }
          ConfigParseResult.failure(s"Unsupported file format: $extension")
      }
    }

    def apply(file: java.io.File): ConfigParseResult[FileSource] = apply(file.toPath)
  }

  /** An in-memory source with optional auxiliary modules. */
  final case class StringSource(
      content: String,
      aux: List[String] = Nil,
      format: Format = Format.Tla)
      extends InputSource {

    override def exists: Boolean = true

    override def readUtf8: ConfigParseResult[String] =
      ConfigParseResult.success(content)

    override def toString: String = s"StringSource(${format.name})"
  }
}
