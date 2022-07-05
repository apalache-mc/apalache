package at.forsyte.apalache.infra.passes

/** Defines the data sources supported in the [[PassOptions]] */
object SourceOption {

  /** Supported data sources */
  sealed trait T

  /** Data to be loaded from a file */
  final case class FileSource(file: java.io.File) extends T

  /** Data supplied as a string */
  final case class StringSource(content: String) extends T
}
