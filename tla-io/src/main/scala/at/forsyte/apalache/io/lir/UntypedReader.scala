package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.{TypeTag, Untyped}

object UntypedReader extends TypeTagReader {
  override def apply(tagStr: String): TypeTag = Untyped()
}
