package at.forsyte.apalache.tla.lir.transformations

import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.io.UTFPrinter

/**
  * A TransformationInvariant causes a Transformation to throw an InvariantViolation when
  * the results of `transform` do not satisfy the predicate defined by `holdsFor`
  */
trait TransformationInvariant extends TransformationListener {
  val name : String

  override def toString : String = name

  def holdsFor( originalEx : TlaEx, newEx : TlaEx ) : Boolean

  override def onTransformation( originalEx : TlaEx, newEx : TlaEx ) : Unit =
    if ( !holdsFor( originalEx, newEx ) )
      throw new InvariantViolation(
        s"Transforming [$originalEx] to [$newEx] violates ${this.toString}."
      )
}

class SimpleTransformationInvariant( val name : String, fn : (TlaEx, TlaEx) => Boolean )
  extends TransformationInvariant {
  override def holdsFor( originalEx : TlaEx, newEx : TlaEx ) = fn( originalEx, newEx )

  def unary_! : SimpleTransformationInvariant =
    new SimpleTransformationInvariant( s"${UTFPrinter.m_not}$name", ( a, b ) => !fn( a, b ) )
}

class InvariantViolation( message : String ) extends Exception( message )