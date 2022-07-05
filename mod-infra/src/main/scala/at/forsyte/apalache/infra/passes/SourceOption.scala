package at.forsyte.apalache.infra.passes

/** Defines the data sources supported in the [[PassOptions]] */
sealed abstract class SourceOption

object SourceOption {

  /** Data to be loaded from a file */
  final case class FileSource(file: java.io.File) extends SourceOption

  /** Data supplied as a string */
  final case class StringSource(content: String) extends SourceOption
}
