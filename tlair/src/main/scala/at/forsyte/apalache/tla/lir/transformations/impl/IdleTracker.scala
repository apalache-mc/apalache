package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.transformations.{TlaDeclTransformation, TlaExTransformation, TransformationTracker}

/**
  * An implementation of TransformationTracker that does not do anything.
  * This class may be useful when no tracking is needed.
  */
class IdleTracker extends TransformationTracker {
  override def trackEx( transformation: TlaExTransformation): TlaExTransformation = {
    transformation
  }

  /**
    * Decorate a declaration transformation with a tracker.
    *
    * @param transformation a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  override def trackDecl(transformation: TlaDeclTransformation): TlaDeclTransformation = {
    transformation
  }

  /**
    * A specialized version of trackDecl, which is tuned to TlaOperDecl.
    *
    * @param transformation a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  override def trackOperDecl(transformation: TlaOperDecl => TlaOperDecl): TlaOperDecl => TlaOperDecl = {
    transformation
  }
}
