package at.forsyte.apalache.tla.imp.src

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx}
import at.forsyte.apalache.tla.lir.transformations.TransformationListener

/**
 * <p>This is a special form of transformation tracker that records the changes directly in the source store.
 * In general, this behavior is discouraged. However, when SanyImporter does code modifications itself,
 * it can only save the changes in the source store. Do not use this class outside of SanyImporter.</p>
 *
 * <p>The long class class name indicates that you should not use this class, unless you know what you are doing.</p>
 *
 * @author Igor Konnov
 */
class SaveToStoreTransformationListener(sourceStore: SourceStore) extends TransformationListener {
  override def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit = {
    if (originalEx.ID != newEx.ID) {
      sourceStore.findOrWarn(originalEx.ID).foreach { loc => sourceStore.add(newEx.ID, loc) }
    }
  }

  override def onDeclTransformation(originalDecl: TlaDecl, newDecl: TlaDecl): Unit = {
    if (originalDecl.ID != newDecl.ID) {
      sourceStore.findOrWarn(originalDecl.ID).foreach { loc => sourceStore.add(newDecl.ID, loc) }
    }
  }
}
