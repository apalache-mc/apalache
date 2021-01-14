package at.forsyte.apalache.tla.imp.src

import at.forsyte.apalache.tla.lir.{TlaDecl, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{TlaDeclTransformation, TlaExTransformation, TransformationTracker}

/**
  * This is a special form of transformation tracker that records the changes directly in the source store.
  * In general, this behavior is discouraged. However, when SanyImporter does code modifications itself,
  * it can only save the changes in the source store. Do not use this class outside of SanyImporter.
  *
  * @author Igor Konnov
  */
class SaveToStoreTracker(sourceStore: SourceStore) extends TransformationTracker {
  /**
    * Decorate a transformation with a tracker.
    *
    * @param tr an expression transformation
    * @return a new transformation that applies tr and tracks the changes
    */
  override def track(tr: TlaExTransformation): TlaExTransformation = {
    input: TlaEx =>
      val output = tr(input)
      if (output.ID != input.ID) {
        sourceStore.findOrLog(input.ID).foreach { loc => sourceStore.add(output.ID, loc) }
      }
      output
  }

  /**
    * Decorate a declaration transformation with a tracker.
    *
    * @param tr a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  override def trackDecl(tr: TlaDeclTransformation): TlaDeclTransformation = {
    input: TlaDecl =>
      val output = tr(input)
      if (output.ID != input.ID) {
        sourceStore.findOrLog(input.ID).foreach { loc => sourceStore.add(output.ID, loc) }
      }
      output
  }

  /**
    * A specialized version of trackDecl, which is tuned to TlaOperDecl.
    *
    * @param tr a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  override def trackOperDecl(tr: TlaOperDecl => TlaOperDecl): TlaOperDecl => TlaOperDecl = {
    input: TlaOperDecl =>
      val output = tr(input)
      if (output.ID != input.ID) {
        sourceStore.findOrLog(input.ID).foreach { loc => sourceStore.add(output.ID, loc) }
      }
      output
  }
}
