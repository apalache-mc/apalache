package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.TlaOperDecl
import at.forsyte.apalache.tla.lir.transformations._

/**
  * TrackerWithListeners tracks a transformation by executing all of its `listeners`' onTransformation,
  * whenever the tracked transformation is executed.
  *
  * For any input x, track(t)(x) and t(x) are equal.
  */
sealed case class TrackerWithListeners(listeners: TransformationListener*)
    extends TransformationTracker {
  override def track(
      transformation: TlaExTransformation
  ): TlaExTransformation = { ex =>
    val newEx = transformation(ex)
    listeners foreach {
      _.onTransformation(ex, newEx)
    }
    newEx
  }

  /**
    * Decorate a declaration transformation with a tracker.
    *
    * @param transformation a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  override def trackDecl(
      transformation: TlaDeclTransformation
  ): TlaDeclTransformation = { decl =>
    val newDecl = transformation(decl)
    listeners foreach { _.onDeclTransformation(decl, newDecl) }
    newDecl
  }

  /**
    * A specialized version of trackDecl, which is tuned to TlaOperDecl.
    *
    * @param transformation a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  override def trackOperDecl(
      transformation: TlaOperDecl => TlaOperDecl
  ): TlaOperDecl => TlaOperDecl = { decl =>
    val newDecl = transformation(decl)
    listeners foreach { _.onDeclTransformation(decl, newDecl) }
    newDecl
  }
}
