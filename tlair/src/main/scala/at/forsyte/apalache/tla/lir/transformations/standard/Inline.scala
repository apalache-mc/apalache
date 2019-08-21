package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaOper}
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
        // Jure, 24.7.19.: This does not establish ChangeTracking between body and inlinedNewBody.
        // Do we want to track these changes?

        // Jure, 29.7.19.: Operator instantiation potentially violates UID uniqueness, e.g. currently, when
        // we instantiate A(p), where A(x) == x + x, both copies of x have the same UID (as p).
        val newBody = params.zip( args ).foldLeft( body ) {
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
    case ex@OperEx( op : TlaUserOper, args@_* ) =>
      instantiateBody( bodyMap, tracker, op.name, args : _* ).getOrElse( ex )
    case ex@OperEx( TlaOper.apply, NameEx( name ), args@_* ) =>
      instantiateBody( bodyMap, tracker, name, args : _* ).getOrElse( ex )
    case ex => ex
  }

  def apply( bodyMap : BodyMap, tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = inlineLeaf( bodyMap, tracker )
    lazy val self = apply( bodyMap, tracker )
    ex match {
      case OperEx( op : LetInOper, body ) =>
        // Inline bodies of all op.defs
        val inlinedOperDecls = op.defs.map { x =>
          x.copy(
            body = self( x.body )
          )
        }

        val newOp = new LetInOper( inlinedOperDecls )
        val newBody = self( body )
        val retEx = if ( op == newOp && body == newBody ) ex else OperEx( newOp, newBody )

        tr( retEx )
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map self
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case LetIn0Ex( name, operBody, exprBody ) =>
        val newOperBody = self(operBody)
        val newExprBody = self(exprBody)
        val newEx =
          if ( newOperBody == operBody && newExprBody == exprBody ) ex
          else LetIn0Ex(name, newOperBody, newExprBody)
        tr( newEx )
      case _ => tr( ex )
    }
  }
}


