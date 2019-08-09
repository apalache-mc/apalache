package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationListener, TransformationTracker}

// TODO: REMOVE?
class TransformationTrackerImpl(listeners : TransformationListener* ) extends TransformationTracker {
  def track( fn : TlaExTransformation ) : TlaExTransformation =
    new TransformationImpl( fn, listeners : _* )

  // suppressInvariantChecks
}
