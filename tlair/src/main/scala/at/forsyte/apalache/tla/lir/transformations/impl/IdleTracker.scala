package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * An implementation of TransformationTracker that does not do anything.
  * This class may be useful when no tracking is needed.
  */
class IdleTracker extends TransformationTracker {
  override def trackEx( transformation: TlaExTransformation): TlaExTransformation = {
    transformation
  }
}
