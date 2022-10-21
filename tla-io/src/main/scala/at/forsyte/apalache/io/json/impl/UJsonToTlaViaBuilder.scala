package at.forsyte.apalache.io.json.impl

import at.forsyte.apalache.io.json.JsonToTlaViaBuilder
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.imp.src.SourceStore

/**
 * @author
 *   Jure Kukovec
 */
class UJsonToTlaViaBuilder(sourceStoreOpt: Option[SourceStore] = None)(implicit typeTagReader: TypeTagReader)
    extends JsonToTlaViaBuilder[UJsonRep](UJsonScalaFactory, sourceStoreOpt)(typeTagReader)
