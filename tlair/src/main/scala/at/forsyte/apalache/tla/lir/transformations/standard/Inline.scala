package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.TlaOper
import at.forsyte.apalache.tla.lir.storage.BodyMap
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

object Inline {
  /**
    * Attempts to instantiate the body of the operator named `name` with the provided arguments.
    * Returns None if the operator name is not a key in `bodyMap`, otherwise returns Some(b), where
    * b is the body of the operator with each formal parameter replaced by the corresponding value from `args`
    *
    * Throws IllegalArgumentException if the size of `args` does not match the operator arity.
    */
  private def instantiateBody(
                               bodyMap : BodyMap,
                               tracker : TransformationTracker,
                               name : String,
                               args : TlaEx*
                             ) : Option[TlaEx] =
    bodyMap.get( name ) match {
      case Some( (params, body) ) if params.size == args.size =>
        // We deep copy the body, to ensure UID uniqueness
        val bodyCopy = DeepCopy( tracker )( body )

        val newBody = params.zip( args ).foldLeft( bodyCopy ) {
          case (b, (fParam, arg)) =>
            ReplaceFixed( NameEx( fParam.name ), arg, tracker )( b )
        }
        // newBody may contain other operator calls
        val inlinedNewBody = Inline( bodyMap, tracker )( newBody )
        Option( inlinedNewBody )
      case Some( (params, _) ) if params.size != args.size =>
        throw new IllegalArgumentException(
          s"Operator $name with arity ${params.size} called with ${args.size} argument(s)."
        )
      case _ => None
    }

  private def inlineLeaf(
                          bodyMap : BodyMap,
                          tracker : TransformationTracker
                        ) : TlaExTransformation = tracker.track {
    // Jure, 5.7.19: Can 0-arity operators ever appear as standalone NameEx, without
    // a OperEx( TlaOper.apply, NameEx( name ), args@_* ) wrapper? Currently, we consider that invalid
    case ex@OperEx( TlaOper.apply, NameEx( name ), args@_* ) =>
      instantiateBody( bodyMap, tracker, name, args : _* ).getOrElse( ex )
    case ex => ex
  }

  def apply( bodyMap : BodyMap, tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = inlineLeaf( bodyMap, tracker )
    lazy val self = apply( bodyMap, tracker )
    ex match {
      case LetInEx( body, defs@_* ) =>
        // Transform bodies of all op.defs
        val newDefs = defs.map { x =>
          x.copy(
            body = self( x.body )
          )
        }
        val newBody = self( body )
        val retEx = if ( defs == newDefs && body == newBody ) ex else LetInEx( newBody, newDefs : _* )
        tr( retEx )

      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map self
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )

      case _ => tr( ex )
    }
  }
}


