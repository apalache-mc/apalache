package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.io.TypeTagPrinter
import at.forsyte.apalache.tla.lir.{TypeTag, Typed, Untyped}

/**
 * TypeTag printer for the Type-1 typesystem.
 */
object TlaType1Printer extends TypeTagPrinter {
  override def apply(tag: TypeTag): String = tag match {
    case Untyped()               => "untyped"
    case Typed(myType: TlaType1) => myType.toString
    case _                       => "<UNDEFINED>"
  }
}
