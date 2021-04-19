package at.forsyte.apalache.tla.lir.io

import at.forsyte.apalache.tla.lir.{TypeTag, Untyped}

/**
 * Recovers TypeTags from their string representations.
 * Inverse of TypeTagPrinter.
 */
trait TypeTagReader {
  def apply(tagStr: String): TypeTag
}

object UntypedReader extends TypeTagReader {
  override def apply(tagStr: String): TypeTag = Untyped()
}
