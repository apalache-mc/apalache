package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.typecheck.parser.DefaultType1Parser
import at.forsyte.apalache.tla.lir.{TypeTag, Typed}
import at.forsyte.apalache.tla.lir.io.TypeTagReader

object Type1TagReader extends TypeTagReader {
  override def apply(tagStr: String): TypeTag = Typed(DefaultType1Parser(tagStr))
}
