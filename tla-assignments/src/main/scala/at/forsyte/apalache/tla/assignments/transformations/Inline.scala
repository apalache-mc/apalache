package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.db.BodyDB
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.transformations._
import at.forsyte.apalache.tla.lir.transformations.impl.{RecursiveTransformationImpl, ReplaceFixed, TransformationTrackerImpl, TransformationImpl}

sealed case class Inline(bodyMap : BodyDB, listeners : TransformationListener* )
  extends TransformationTrackerImpl( listeners : _* ) {

  /**
    * Attempts to instantiate the body of the operator named `name` with the provided arguments.
    * Returns None if the operator name is not a key in `bodyMap`, otherwise returns Some(b), where
    * b is the body of the operator with each formal parameter replaced by the corresponding value from `args`
    *
    * Throws IllegalArgumentException if the size of `args` does not match the operator arity.
    */
  private def instantiateBody( name : String, args : TlaEx* ) : Option[TlaEx] =
    bodyMap.get( name ) match {
      case Some( (params, body) ) if params.size == args.size =>
        val newBody = params.zip( args ).foldLeft( body ) { case (b, (fParam, arg)) =>
          val replacement : TransformationImpl = ReplaceFixed( NameEx( fParam.name ), arg, listeners : _* )
          new RecursiveTransformationImpl( replacement ).transform( b )
        }
        Option( newBody )
      case Some( (params, _) ) if params.size != args.size =>
        throw new IllegalArgumentException(
          s"Operator $name with arity ${params.size} called with ${args.size} argument(s)."
        )
      case _ => None
    }

  /**
    * There are 2 ways one may call a custom operator,
    * either with TlaOper.apply and the operator name, or as a
    * TlaUserOper directly.
    */
  val InlineOne : ExprTransformer = track {
    case ex@OperEx( op : TlaUserOper, args@_* ) =>
      instantiateBody( op.name, args : _* ).getOrElse( ex )
    case ex@OperEx( TlaOper.apply, NameEx( name ), args@_* ) =>
      instantiateBody( name, args : _* ).getOrElse( ex )
    case ex => ex
  }

  val InlineAllToplevel : ExprTransformer =
    new RecursiveTransformationImpl( InlineOne )

  private def lambda( ex : TlaEx ) : TlaEx = {
    val post = InlineAllToplevel( ex )
    if ( post == ex ) ex else lambda( post )
  }

  /**
    * The InlineAll transformation replaces all cal-by-name occurrences of operators in `bodyMap`
    * with their operator bodies, where formal parameters are instantiated with the call arguments
    *
    * Example:
    *
    * A(x) == x + 2
    * B == IF A(y) > 7 THEN 1 ELSE 0
    *
    * InlineAll(B) = IF y + 2 > 7 THEN 1 ELSE 0
    */
  val InlineAll: ExprTransformer = track {
    lambda
  }
}
