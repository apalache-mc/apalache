package at.forsyte.apalache.tla.lir.transformations

/**
  * An implementation of this trait wraps an expression transformer with the code that somehow tracks the transformation.
  * For instance, it can wrap a transformation with calls to transformation listeners.
  *
  * @author Igor Konnov
  */
trait TransformationTracker {
  def track(t: TlaExTransformation): TlaExTransformation
}
