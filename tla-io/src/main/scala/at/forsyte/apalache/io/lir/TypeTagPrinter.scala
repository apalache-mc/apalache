package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.TypeTag

/**
 * Defines string representations for TypeTag objects.
 */
trait TypeTagPrinter {
  def apply(tag: TypeTag): String
}
