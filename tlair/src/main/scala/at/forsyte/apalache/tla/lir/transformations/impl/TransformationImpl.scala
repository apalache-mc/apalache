package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationListener}

/**
  * A Transformation is a wrapper around a TlaEx => TlaEx function, that
  * is equipped with any number of TransformationListener instances (e.g. TransformationInvariant%s)
  *
  * TODO: Igor @ 01.07.2019: the problem with this class is that it mixes two separate concepts:
  * (1) a transformation as a function TlaEx => TlaEx, and (2) the listeners that are attached to this transformation.
  * For the API client, a transformation is just TlaEx => TlaEx, nothing more. How this actual transformation works
  * is an implementation detail.
  */
class TransformationImpl(fn : TlaEx => TlaEx, listeners : TransformationListener*)
    extends TlaExTransformation {
  // TODO: Igor @ 01.07.2019? Why do we need this method? I would even declare Transformation sealed, to disable inheritance.
  def transform( ex : TlaEx ) : TlaEx = {
    val res = fn( ex )
    listeners foreach {
      _.onTransformation( ex, res )
    }
    res
  }

  def apply( ex : TlaEx ) : TlaEx = transform( ex )

  /**
    * Invariant checks may be disabled for faster execution time, since
    * invariant listeners only perform validation, not data manipulation
    *
    * TODO: Igor @ 01.07.2019: this method should not be in Transformation.
    * All operations with listeners should be done in TransformationTrackerImpl.
    */
  def suppressInvariantChecks : TransformationImpl =
    new TransformationImpl( fn, listeners.filterNot( _.isInstanceOf[TransformationInvariant] ) :_* )
}
