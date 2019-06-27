package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{RecursiveProcessor, TlaEx}

class RecursiveTransformation( transformation : Transformation ) extends Transformation {
  // transformation already defines listeners
  override val listeners : Seq[TransformationListener] = Seq.empty

  override def transformInternal( ex : TlaEx ) : TlaEx =
    RecursiveProcessor.transformTlaEx(
      RecursiveProcessor.DefaultFunctions.naturalTermination,
      transformation.transform,
      transformation.transform
    )( ex )
}
