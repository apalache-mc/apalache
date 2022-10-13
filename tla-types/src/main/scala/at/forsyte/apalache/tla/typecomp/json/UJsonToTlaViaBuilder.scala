package at.forsyte.apalache.tla.typecomp.json

import at.forsyte.apalache.io.json.impl.{UJsonRep, UJsonScalaFactory}
import at.forsyte.apalache.io.lir.TypeTagReader
import at.forsyte.apalache.tla.imp.src.SourceStore

/**
 * @author
 *   Jure Kukovec
 */
class UJsonToTlaViaBuilder(sourceStoreOpt: Option[SourceStore] = None)(implicit typeTagReader: TypeTagReader)
    extends JsonToTlaViaBuilder[UJsonRep](UJsonScalaFactory, sourceStoreOpt)(typeTagReader)
