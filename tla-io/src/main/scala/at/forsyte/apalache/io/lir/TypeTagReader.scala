package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.TypeTag

/**
 * Recovers TypeTags from their string representations.
 * Inverse of TypeTagPrinter.
 */
trait TypeTagReader {
  def apply(tagStr: String): TypeTag
}
