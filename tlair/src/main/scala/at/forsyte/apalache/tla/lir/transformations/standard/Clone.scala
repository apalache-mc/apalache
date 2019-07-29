package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

// Tracks deepCopy
object Clone {
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.track { _.deepCopy()}
}
