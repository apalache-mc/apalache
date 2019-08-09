package at.forsyte.apalache.tla.lir.transformations.impl

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.io.UTFPrinter
import at.forsyte.apalache.tla.lir.transformations.TransformationListener

/**
  * TODO: REMOVE?
  *
  * A TransformationInvariant causes a Transformation to throw an InvariantViolation when
  * the results of `transform` do not satisfy the predicate defined by `holdsFor`.
  *
  * TODO: Igor @ 01.07.2019: what is the added value of this class?
  * I could write my own TransformationListener that check whatever properties I like.
  * If you like to filter out the invariant tests, you could define a trait TransformationInvariant,
  * without overriding onTransformation. We should keep the class hierarchy small and simple.
  */
class TransformationInvariant(
                             val name: String,
                             val holdsFor: (TlaEx, TlaEx) => Boolean
                             ) extends TransformationListener {
  override def toString : String = name

  override def onTransformation( originalEx : TlaEx, newEx : TlaEx ) : Unit =
    if ( !holdsFor( originalEx, newEx ) )
      throw new InvariantViolation(
        s"Transforming [$originalEx] to [$newEx] violates ${this.toString}."
      )

  def unary_! : TransformationInvariant =
    new TransformationInvariant( s"${UTFPrinter.m_not}$name", !holdsFor( _, _ ) )
}

// TODO: Igor @ 01.07.2019: the name of this class does not really matter,
// as this is going to be a pretty much lethal exception, which cannot be handled.
// TODO: Igor @ 01.07.2019: Shall we introduce TransformationError(message: String, origin: TlaEx) instead?
// Then the top-level code would show the problematic code point and the message.
// TransformationError could be used as a general-purpose error.
class InvariantViolation( message : String ) extends Exception( message )