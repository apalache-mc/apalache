package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.oper._
import at.forsyte.apalache.tla.lir.transformations._

object PruneApalacheAnnotations {
  private def pruneOne( tracker : TransformationTracker ) : TlaExTransformation =
    tracker.trackEx {
      case OperEx( BmcOper.withType, arg, typeAnnotation ) => arg
      case e => e
    }

  /**
    * Returns a transformation that removes all Apalache operators (e.g. BMC!<:).
    *
    * Example:
    * S <: {Int} -> S
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.trackEx { ex =>
    val tr = pruneOne( tracker )
    lazy val self = apply( tracker )
    ex match {
      case LetInEx( body, defs@_* ) =>
        // Transform bodies of all op.defs
        val newDefs = defs map tracker.trackOperDecl { d => d.copy(body = self(d.body)) }
        val newBody = self( body )
        val retEx = if ( defs == newDefs && body == newBody ) ex else LetInEx( newBody, newDefs : _* )
        tr( retEx )

      case OperEx( op, args@_* ) =>
        val newArgs = args map self
        val newEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( newEx )

      case _ => tr( ex )
    }
  }
}
