package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonToTla
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.io.lir.TypeTagReader

/**
 * A json decoder, using the UJson representation
 */
class UJsonToTla(sourceStoreOpt: Option[SourceStore] = None)(implicit typeTagReader: TypeTagReader)
    extends JsonToTla[UJsonRep](UJsonScalaFactory, sourceStoreOpt)(typeTagReader)
