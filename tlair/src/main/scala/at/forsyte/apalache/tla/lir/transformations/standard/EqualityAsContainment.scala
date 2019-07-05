package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.oper.{LetInOper, TlaActionOper, TlaOper, TlaSetOper}
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
  def apply( tracker : TransformationTracker ) : TlaExTransformation = { ex =>
    val tr = oneEqualityAsContainment( tracker )
    // No need to call tracker.track again, tr is always called on the top-level expression
    ex match {
      case OperEx( op: LetInOper, body ) =>
        // do something with op.decls
        // ...
        tr( apply(tracker)(body) )
      case OperEx( op, args@_* ) =>
        val newArgs = args map apply(tracker)
        val newEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( newEx )
      case _ => tr( ex )
    }
  }
}
