package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.TlaToJson
import at.forsyte.apalache.tla.lir.io.TypeTagPrinter

/**
 * A json encoder, using the UJson representation
 */
class TlaToUJson(implicit typTagPrinter: TypeTagPrinter) extends TlaToJson[UJsonRep](UJsonFactory)(typTagPrinter)
