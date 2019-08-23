package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetInEx, OperEx}
import at.forsyte.apalache.tla.lir.oper.{TlaActionOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.transformations._

object EqualityAsContainment {
  private def oneEqualityAsContainment( tracker : TransformationTracker ) : TlaExTransformation =
    tracker.track {
      case OperEx( TlaOper.eq, lhs@OperEx( TlaActionOper.prime, _ ), rhs ) =>
        OperEx( TlaSetOper.in, lhs, OperEx( TlaSetOper.enumSet, rhs ) )
      case e => e
    }

  /**
    * Returns a transformation that replaces prime assignments with set membership.
    *
    * Example:
    * x' = y --> x' \in {y}
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = oneEqualityAsContainment( tracker )
    lazy val self = apply(tracker)
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

      case OperEx( op, args@_* ) =>
        val newArgs = args map self
        val newEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( newEx )

      case _ => tr( ex )
    }
  }
}
