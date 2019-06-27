package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

class TransformationComposition( transformations : Transformation* ) extends Transformation {
  // Each transformation defines its own listeners
  override val listeners : Seq[TransformationListener] = Seq.empty

  override def transformInternal( ex : TlaEx ) =
    transformations.foldLeft( ex ) { case (e, tr) => tr( e ) }
}
