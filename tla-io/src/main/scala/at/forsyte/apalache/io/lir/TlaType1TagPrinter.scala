package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.{TlaType1, TypeTag, Typed, Untyped}

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
