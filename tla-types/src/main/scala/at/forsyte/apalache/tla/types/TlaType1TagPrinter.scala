package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{TypeTag, Typed, Untyped}
import at.forsyte.apalache.tla.lir.io.TypeTagPrinter
import at.forsyte.apalache.tla.typecheck.TlaType1

class TlaType1TagPrinter extends TypeTagPrinter {
  def apply(tag: TypeTag): String = {
    tag match {
      case Untyped()           => "Untyped"
      case Typed(tt: TlaType1) => tt.toString
      // treat an unknown type as untyped
      case Typed(other) => "Untyped"
    }
  }
}

object TlaType1PrinterPredefs {
  implicit val printer: TypeTagPrinter = new TlaType1TagPrinter
}
