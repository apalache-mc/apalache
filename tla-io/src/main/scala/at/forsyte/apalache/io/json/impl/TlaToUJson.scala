package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.TlaToJson
import at.forsyte.apalache.io.lir.TypeTagPrinter
import at.forsyte.apalache.tla.lir.storage.SourceLocator
import at.forsyte.apalache.tla.lir.TlaModule
import at.forsyte.apalache.io.lir.TlaType1PrinterPredefs.printer // Required as implicit parameter to JsonTlaWRiter

/**
 * A json encoder, using the UJson representation
 */
class TlaToUJson(
    locatorOpt: Option[SourceLocator] = None
  )(implicit typeTagPrinter: TypeTagPrinter)
    extends TlaToJson[UJsonRep](UJsonFactory, locatorOpt)(typeTagPrinter)

object TlaToUJson {
  def apply(module: TlaModule): ujson.Value = (new TlaToUJson()).makeRoot(Seq(module)).value

  implicit val ujsonView: TlaModule => ujson.Value = TlaToUJson(_)
}
