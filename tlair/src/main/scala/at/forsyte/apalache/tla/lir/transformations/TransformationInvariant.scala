package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.io.UTFPrinter

/**
  * A TransformationInvariant causes a Transformation to throw an InvariantViolation when
  * the results of `transform` do not satisfy the predicate defined by `holdsFor`
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

class InvariantViolation( message : String ) extends Exception( message )