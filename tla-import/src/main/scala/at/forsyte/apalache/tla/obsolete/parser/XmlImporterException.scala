package at.forsyte.apalache.tla.obsolete.parser

/**
 * A general exception reported by XmlImporter
  *
  * @deprecated
 *
 * @author konnov
 */
class XmlImporterException(val message: String)
  extends Exception(message)
