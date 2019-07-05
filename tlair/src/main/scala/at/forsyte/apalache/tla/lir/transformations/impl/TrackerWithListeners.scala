package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.transformations._

/**
  * TrackerWithListeners tracks a transformation by executing all of its `listeners`' onTransformation,
  * whenever the tracked transformation is executed.
  *
  * For any input x, track(t)(x) and t(x) are equal.
  */
sealed case class TrackerWithListeners( listeners : TransformationListener* )
  extends TransformationTracker {
  override def track( transformation : TlaExTransformation ) : TlaExTransformation = {
    ex =>
      val newEx = transformation( ex )
      listeners foreach {
        _.onTransformation( ex, newEx )
      }
      newEx
  }

}
