package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.{TlaEx, TlaOperDecl}

/**
  * An implementation of this trait wraps an expression transformer with the code that somehow tracks the transformation.
  * For instance, it can wrap a transformation with calls to transformation listeners.
  *
  * @author Igor Konnov
  */
trait TransformationTracker {

  /**
    * Decorate a transformation with a tracker.
    *
    * @param tr an expression transformation
    * @return a new transformation that applies tr and tracks the changes
    */
  def trackEx(tr: TlaExTransformation): TlaExTransformation

  /**
    * Decorate a declaration transformation with a tracker.
    *
    * @param tr a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  def trackDecl(tr: TlaDeclTransformation): TlaDeclTransformation

  /**
    * A specialized version of trackDecl, which is tuned to TlaOperDecl. Most transformation apply only to
    * user-defined operators. That is why we have added a specialized method for it.
    *
    * @param tr a declaration transformation
    * @return a new declaration transformation that applies tr and tracks the changes
    */
  def trackOperDecl(tr: TlaOperDecl => TlaOperDecl): TlaOperDecl => TlaOperDecl

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
    def tr(f: TlaEx): TlaEx = to
    trackEx(tr)(from)
  }

  /**
    * <p>This adapter method takes an expression transformation and turns it into a declaration transformation that:</p>
    * <ol>
    *   <li>Copies the declaration body and applies the expression transformation to it, and</li>
    *   <li>Tracks the update of the declaration.</li>
    *
    * <p>We provide this method for convenience, because in many cases the operator body is the only thing that changes
    *    in an operator declaration.</p>
    *
    * @param transformation expression transformation
    * @return a declaration transformation that is tracking updates to declarations and expressions inside them.
    */
  def fromExToDeclTransformation(
      transformation: TlaExTransformation
  ): TlaDeclTransformation =
    trackDecl {
      case d @ TlaOperDecl(_, _, b) =>
        d.copy(body = transformation(b))

      case d =>
        d
    }

}
