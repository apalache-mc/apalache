package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir.{TlaType1, TypeTag, Typed, Untyped}

class TlaType1TagPrinter extends TypeTagPrinter {
  def apply(tag: TypeTag): String = {
    tag match {
      case Untyped             => "Untyped"
      case Typed(tt: TlaType1) => tt.toString
      // IrGenerators generates type with arbitrary integers. In order not to crash JSON (en|de)coding tests,
      // we need to not throw on this variant of Typed, but we erase the type with Untyped
      case Typed(_: Int) => "Untyped"
      // unexpected type, output as much as we can
      case Typed(_) => "Typed[%s](%s)".format(tag.getClass.getSimpleName, tag)
    }
  }
}
