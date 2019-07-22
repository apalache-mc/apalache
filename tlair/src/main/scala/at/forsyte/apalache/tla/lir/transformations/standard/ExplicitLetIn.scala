package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}
import at.forsyte.apalache.tla.lir.OperEx
import at.forsyte.apalache.tla.lir.storage.BodyMapFactory

object ExplicitLetIn {

  private def letInExplicitLeaf( tracker : TransformationTracker ) : TlaExTransformation = tracker.track {
    case OperEx( oper : LetInOper, body ) =>

      /** Let-in may be nested */
      val fullyExplicit = apply( tracker )( body )

      /** Make a fresh temporary DB, store all decls inside */
      val bodyDB = BodyMapFactory.makeFromDecls( oper.defs )

      /** Inline as if operators were external. */
      Inline( bodyDB, tracker )( fullyExplicit )
    case ex => ex
  }

  /**
    * Returns a transformation which replaces all occurrences of LET-IN expressions with
    * instances equivalents of their bodies, in which LET-IN defined operators have been expanded
    *
    * Example:
    * LET X(a) == a + b IN X(0) > 1 --> 1 + b > 1
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = { ex =>
    val tr = letInExplicitLeaf( tracker )
    lazy val self = apply( tracker )
    // No need to call tracker.track again, tr is always called on the top-level expression
    ex match {
      case OperEx( op : LetInOper, _ ) =>
        tr( ex )
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map self
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr( ex )
    }
  }
}
