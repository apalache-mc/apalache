package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx

/**
  * An implementation of this trait wraps an expression transformer with the code that somehow tracks the transformation.
  * For instance, it can wrap a transformation with calls to transformation listeners.
  *
  * @author Igor Konnov
  */
trait TransformationTracker {
  /**
    * Decorate a transformation with a tracker.
    * @param tr an expression transformation
    * @return a new transformation that applies tr and tracks the changes
    */
  def trackEx( tr: TlaExTransformation): TlaExTransformation

  /**
    * Sometimes, one has to track a change in a temporary expression that will get transformed into something else
    * before it gets a chance to get tracked with `track`, which only works with end-to-end transformations.
    * In this case, we have to record the change as a side effect and return the new expression.
    * Avoid using this method by default. This is a second-chance method.
    *
    * @param from the original expression
    * @param to the new expression
    * @return the new expression
    */
  def hold(from: TlaEx, to: TlaEx): TlaEx = {
    def tr(f : TlaEx): TlaEx = to
    trackEx(tr)(from)
  }
}
