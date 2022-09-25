package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.UID

/**
 * <p>Type checker calls the listener on important events:</p>
 *
 * <ol> <li>the type of a new expression has been computed, or </li> <li>a type error has been found.</li> </ol>
 *
 * @author
 *   Igor Konnov
 */
abstract class SourceAwareTypeCheckerListener(sourceStore: SourceStore, changeListener: ChangeListener)
    extends TypeCheckerListener {

  protected def findLoc(id: UID): String = {
    val sourceLocator: SourceLocator = SourceLocator(sourceStore.makeSourceMap, changeListener)

    sourceLocator.sourceOf(id) match {
      case Some(loc) => loc.toString
      case None      => "unknown location"
    }
  }
}
