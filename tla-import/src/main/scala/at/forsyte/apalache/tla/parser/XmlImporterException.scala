package at.forsyte.apalache.tla.parser

/**
 * A general exception reported by XmlImporter
  *
  * @deprecated
 *
 * @author konnov
 */
class XmlImporterException(val message: String)
  extends Exception(message)
