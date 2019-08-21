package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetIn0Ex, OperEx}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations._

object PruneApalacheAnnotations {
  private def pruneOne( tracker : TransformationTracker ) : TlaExTransformation =
    tracker.track {
      case OperEx( BmcOper.withType, arg, typeAnnotation ) => arg
      case e => e
    }

  /**
    * Returns a transformation that removes all Apalache operators (e.g. BMC!<:).
    *
    * Example:
    * S <: {Int} -> S
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = pruneOne( tracker )
    lazy val self = apply( tracker )
    ex match {
      case OperEx( op : LetInOper, body ) =>
        // Transform bodies of all op.defs
        val replacedOperDecls = op.defs.map { x =>
          x.copy(
            body = self( x.body )
          )
        }

        val newOp = new LetInOper( replacedOperDecls )
        val newBody = self( body )
        val retEx = if ( op == newOp && body == newBody ) ex else OperEx( newOp, newBody )

        tr( retEx )
      case OperEx( op, args@_* ) =>
        val newArgs = args map self
        val newEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( newEx )
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
