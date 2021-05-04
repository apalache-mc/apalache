package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.TlaToJson
import at.forsyte.apalache.io.lir.TypeTagPrinter
import at.forsyte.apalache.tla.lir.storage.SourceLocator

/**
 * A json encoder, using the UJson representation
 */
class TlaToUJson(locatorOpt: Option[SourceLocator] = None)(
    implicit typeTagPrinter: TypeTagPrinter
) extends TlaToJson[UJsonRep](UJsonFactory, locatorOpt)(typeTagPrinter)
