package at.forsyte.apalache.io.lir

object TlaType1PrinterPredefs {
  implicit val printer: TypeTagPrinter = new TlaType1TagPrinter
}
