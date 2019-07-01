package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.transformations.{ExprTransformer, TransformationListener, TransformationTracker}

class TransformationTrackerImpl(listeners : TransformationListener* ) extends TransformationTracker {
  def track( fn : ExprTransformer ) : ExprTransformer =
    new TransformationImpl( fn, listeners : _* )
}
