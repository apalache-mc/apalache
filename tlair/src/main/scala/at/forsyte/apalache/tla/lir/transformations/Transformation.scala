package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A Transformation is a wrapper around a TlaEx => TlaEx function, that
  * is equipped with any number of TransformationListener instances (e.g. TransformationInvariant%s)
  */
class Transformation(
                      fn : TlaEx => TlaEx,
                      listeners : TransformationListener*
                    ) {
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
    */
  def suppressInvariantChecks : Transformation =
    new Transformation( fn, listeners.filterNot( _.isInstanceOf[TransformationInvariant] ) :_* )
}
