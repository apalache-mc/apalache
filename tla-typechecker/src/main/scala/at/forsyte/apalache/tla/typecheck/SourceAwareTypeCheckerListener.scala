package at.forsyte.apalache.tla.typecheck

import at.forsyte.apalache.tla.lir.storage.{ChangeListener, SourceLocator}
import at.forsyte.apalache.tla.imp.src.SourceStore
import at.forsyte.apalache.tla.lir.UID

/** A [[TypeCheckerListener]] that has a source store and and a change listener */
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
