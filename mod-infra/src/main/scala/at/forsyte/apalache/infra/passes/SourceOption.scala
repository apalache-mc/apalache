package at.forsyte.apalache.infra.passes

/** Defines the data sources supported in the [[PassOptions]] */
object SourceOption {

  /** Supported data sources */
  sealed trait T

  /** Data to be loaded from a file */
  case class File(file: java.io.File) extends T

  /** Data supplied as a string */
  case class String(content: java.lang.String) extends T
}
