package at.forsyte.apalache.tla.ir

/**
 * A basic entry found in XML code of TLA+ code as constructed by tla2sany.XMLExporter
 *
 * @see tla2sany.XMLExporter
 *
 * @author konnov
 */
trait BaseEntry {
  val uid: Int
  val uniqueName: String
  val origin: Option[Origin]
}
