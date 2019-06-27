package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * If `condition` holds, performs `transformation`, otherwise acts as the identity transformation
  */
class ConditionalTransformation( condition : TlaEx => Boolean,
                                 transformation : Transformation
                               ) extends Transformation {
  // transformation already defines listeners
  override val listeners : Seq[TransformationListener] = Seq.empty

  override def transformInternal( ex : TlaEx ) : TlaEx =
    if ( condition( ex ) ) transformation( ex ) else ex
}