package at.forsyte.apalache.tla.types

import at.forsyte.apalache.tla.lir.{TlaType1, TypeTag, Typed, Untyped}
import at.forsyte.apalache.tla.lir.io.TypeTagPrinter

class TlaType1TagPrinter extends TypeTagPrinter {
  def apply(tag: TypeTag): String = {
    tag match {
      case Untyped()           => "Untyped"
      case Typed(tt: TlaType1) => tt.toString
      // unexpected type, output as much as we can
      case Typed(_) => "Typed[%s](%s)".format(tag.getClass.getSimpleName, tag)
    }
  }
}

object TlaType1PrinterPredefs {
  implicit val printer: TypeTagPrinter = new TlaType1TagPrinter
}
