package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * Many processing methods transform a TLA+ expression into another TLA+ expression. To record these changes,
  * we have introduced this listener. This is a replacement for SourceDB.
  *
  * @author Igor Konnov
  */
trait TransformationListener {
  def onTransformation(originalEx: TlaEx, newEx: TlaEx): Unit
}

