package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A Transformation is a wrapper around a TlaEx => TlaEx function, that
  * is equipped with any number of TransformationListener instances (e.g. TransformationInvariant%s)
  */
trait Transformation {
  def transform( ex : TlaEx ) : TlaEx = {
    val res = transformInternal( ex )
    listeners foreach {
      _.onTransformation( ex, res )
    }
    res
  }

  def apply( ex : TlaEx ) : TlaEx = transform( ex )

  def transformInternal( ex : TlaEx ) : TlaEx

  val listeners : Seq[TransformationListener]
}

class SimpleTransformation( fn : TlaEx => TlaEx, val listeners : TransformationListener* )
  extends Transformation {

  override def transformInternal( ex : TlaEx ) : TlaEx = fn( ex )

  /**
    * Invariant checks may be disabled for faster execution time, since
    * invariant listeners only perform validation, not data manipulation
    */
  def suppressInvariantChecks : SimpleTransformation =
    new SimpleTransformation( fn, listeners.filterNot( _.isInstanceOf[TransformationInvariant] ) : _* )
}
