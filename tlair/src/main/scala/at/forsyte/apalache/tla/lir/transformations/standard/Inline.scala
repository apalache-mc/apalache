package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.db.BodyDB
import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaOper}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, _}

object Inline {
  /**
    * Attempts to instantiate the body of the operator named `name` with the provided arguments.
    * Returns None if the operator name is not a key in `bodyMap`, otherwise returns Some(b), where
    * b is the body of the operator with each formal parameter replaced by the corresponding value from `args`
    *
    * Throws IllegalArgumentException if the size of `args` does not match the operator arity.
    */
  private def instantiateBody(
                               bodyMap : BodyDB,
                               tracker : TransformationTracker,
                               name : String,
                               args : TlaEx*
                             ) : Option[TlaEx] =
    bodyMap.get( name ) match {
      case Some( (params, body) ) if params.size == args.size =>
        val newBody = params.zip( args ).foldLeft( body ) {
          case (b, (fParam, arg)) =>
            ReplaceFixed( NameEx( fParam.name ), arg, tracker )( b )
        }
        // newBody may contain other operator calls
        val inlinedNewBody = Inline(bodyMap, tracker)(newBody)
        Option( inlinedNewBody )
      case Some( (params, _) ) if params.size != args.size =>
        throw new IllegalArgumentException(
          s"Operator $name with arity ${params.size} called with ${args.size} argument(s)."
        )
      case _ => None
    }

  private def inlineLeaf(
                          bodyMap : BodyDB,
                          tracker : TransformationTracker
                        ) : TlaExTransformation = tracker.track {
    // Jure, 5.7.19: Can 0-arity operators ever appear as standalone NameEx, without
    // a OperEx( TlaOper.apply, NameEx( name ), args@_* ) wrapper? Currently, we consider that invalid
    case ex@OperEx( op : TlaUserOper, args@_* ) =>
      instantiateBody( bodyMap, tracker, op.name, args : _* ).getOrElse( ex )
    case ex@OperEx( TlaOper.apply, NameEx( name ), args@_* ) =>
      instantiateBody( bodyMap, tracker, name, args : _* ).getOrElse( ex )
    case ex => ex
  }

  def apply( bodyMap : BodyDB, tracker : TransformationTracker ) : TlaExTransformation = { ex =>
    val tr = inlineLeaf( bodyMap, tracker )
    // No need to call tracker.track again, tr is always called on the top-level expression
    ex match {
      case OperEx( op : LetInOper, body ) =>
        // do something with op.decls
        // ...
        tr( apply(bodyMap, tracker)(body) )
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map apply(bodyMap, tracker)
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr( ex )
    }
  }
}


