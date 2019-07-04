package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.db.BodyDBFactory
import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.impl.{RecursiveTransformationImpl, TransformationImpl, TransformationTrackerImpl}
import at.forsyte.apalache.tla.lir.transformations.{ExprTransformer, TransformationListener}

sealed case class LetInExplicit(listeners : TransformationListener* )
  extends TransformationTrackerImpl( listeners : _* ) {
  val LetInExplicitOnce : ExprTransformer = track {
    case OperEx( oper : LetInOper, body ) =>

      /** Make a fresh temporary DB, store all decls inside */
      val bodyDB = BodyDBFactory.makeDBFromDecls( oper.defs )

      /**
        * Inline as if operators were external.
        */
      Inline( bodyDB, listeners : _* ).InlineAll( body )
    case ex => ex
  }

  private def lambda( ex : TlaEx ) : TlaEx = {
    val post = LetInExplicitOnce( ex )
    if ( post == ex ) ex else lambda( post )
  }

  /**
    * Recursive call to LetInExplicitOnce is needed because LET-IN may be nested
    */
  val LetInExplicitAllToplevel : ExprTransformer = track {
    lambda
  }


  /**
    * The AllLetInExplicit transformation replaces all occurrences of LET-IN-defined
    * operators with their bodies.
    *
    * Example:
    *
    * A == LET B(x) == x + 2 IN B(3) + 1
    *
    * AllLetInExplicit(A) = x + 2 + 1
    */
  val AllLetInExplicit : TransformationImpl =
    new RecursiveTransformationImpl( LetInExplicitAllToplevel )
}
