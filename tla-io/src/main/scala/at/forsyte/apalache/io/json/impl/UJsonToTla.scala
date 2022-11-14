package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonToTla
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.imp.src.SourceStore

/**
 * @author
 *   Jure Kukovec
 */
class UJsonToTla(sourceStoreOpt: Option[SourceStore] = None)(implicit typeTagReader: TypeTagReader)
    extends JsonToTla[UJsonRep](UJsonScalaFactory, sourceStoreOpt)(typeTagReader)
