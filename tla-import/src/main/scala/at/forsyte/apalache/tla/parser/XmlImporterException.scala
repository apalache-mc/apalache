package at.forsyte.apalache.tla.parser

/**
 * A general exception reported by XmlImporter
 *
 * @author konnov
 */
class XmlImporterException(val message: String)
  extends Exception(message)
