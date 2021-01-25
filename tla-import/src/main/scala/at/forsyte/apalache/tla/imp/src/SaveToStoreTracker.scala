package at.forsyte.apalache.tla.imp.src

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

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
  override def trackEx( tr: TlaExTransformation): TlaExTransformation = {
    input: TlaEx =>
      val output = tr(input)
      if (output.ID != input.ID) {
        sourceStore.findOrLog(input.ID).foreach { loc => sourceStore.add(output.ID, loc) }
      }
      output
  }
}
