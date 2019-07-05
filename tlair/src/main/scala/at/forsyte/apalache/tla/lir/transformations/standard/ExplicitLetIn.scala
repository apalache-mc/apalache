package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.db.BodyDBFactory
import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.impl.{RecursiveTransformationImpl, TrackerWithListeners, TransformationImpl, TransformationTrackerImpl}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationListener, TransformationTracker}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

object ExplicitLetIn {

  def letInExplicitLeaf( tracker : TransformationTracker ) : TlaExTransformation = tracker.track {
    case OperEx( oper : LetInOper, body ) =>

      /** Let-in may be nested */
      val fullyExplicit = apply( tracker )( body )

      /** Make a fresh temporary DB, store all decls inside */
      val bodyDB = BodyDBFactory.makeDBFromDecls( oper.defs )

      /** Inline as if operators were external. */
      Inline( bodyDB, tracker )( fullyExplicit )
    case ex => ex
  }


  def apply( tracker : TransformationTracker ) : TlaExTransformation = { ex =>
    val tr = letInExplicitLeaf( tracker )
    // No need to call tracker.track again, tr is always called on the top-level expression
    ex match {
      case OperEx( op : LetInOper, _ ) =>
        tr( ex )
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map apply( tracker )
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr( ex )
    }
  }
}

//
//sealed case class ExplicitLetIn( listeners : TransformationListener* )
//  extends TransformationTrackerImpl( listeners : _* ) {
//  val LetInExplicitOnce : TlaExTransformation = track {
//    case OperEx( oper : LetInOper, body ) =>
//
//      /** Make a fresh temporary DB, store all decls inside */
//      val bodyDB = BodyDBFactory.makeDBFromDecls( oper.defs )
//
//      /**
//        * Inline as if operators were external.
//        */
//      Inline( bodyDB, TrackerWithListeners( listeners : _* ) )( body )
//    case ex => ex
//  }
//
//  private def lambda( ex : TlaEx ) : TlaEx = {
//    val post = LetInExplicitOnce( ex )
//    if ( post == ex ) ex else lambda( post )
//  }
//
//  /**
//    * Recursive call to LetInExplicitOnce is needed because LET-IN may be nested
//    */
//  val LetInExplicitAllToplevel : TlaExTransformation = track {
//    lambda
//  }
//
//
//  /**
//    * The AllLetInExplicit transformation replaces all occurrences of LET-IN-defined
//    * operators with their bodies.
//    *
//    * Example:
//    *
//    * A == LET B(x) == x + 2 IN B(3) + 1
//    *
//    * AllLetInExplicit(A) = x + 2 + 1
//    */
//  val AllLetInExplicit : TransformationImpl =
//    new RecursiveTransformationImpl( LetInExplicitAllToplevel )
//}
