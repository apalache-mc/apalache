package at.forsyte.apalache.io.json.ujsonimpl

import at.forsyte.apalache.io.json.JsonToTla
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.imp.src.SourceStore

/**
 * A json decoder, using the UJson representation
 */
class UJsonToTla(sourceStoreOpt: Option[SourceStore] = None)(implicit typeTagReader: TypeTagReader)
    extends JsonToTla[UJsonRepresentation](ScalaFromUJsonAdapter, sourceStoreOpt)(typeTagReader)
