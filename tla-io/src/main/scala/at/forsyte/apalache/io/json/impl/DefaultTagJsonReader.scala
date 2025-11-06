package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonDeserializationError
import at.forsyte.apalache.tla.lir.{TypeTag, Typed, Untyped}
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.types.parser.{DefaultType1Parser, Type1ParseError}

object DefaultTagJsonReader extends TypeTagReader {
  override def apply(tagStr: String): TypeTag = {
    tagStr match {
      case "Untyped" => Untyped
      case s         =>
        try {
          Typed(DefaultType1Parser(tagStr))
        } catch {
          case _: Type1ParseError =>
            throw new JsonDeserializationError(
                s"Error in type annotation: Expected Type1 expression or 'Untyped', found: $s"
            )
        }
    }
  }
}
