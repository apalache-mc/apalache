package at.forsyte.apalache.tla.assignments.transformations

import at.forsyte.apalache.tla.lir.control.LetInOper
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.db.BodyDBFactory
import at.forsyte.apalache.tla.lir.transformations.{RecursiveTransformation, Transformation, TransformationFactory, TransformationListener}

sealed case class LetInExplicitFactory( listeners : TransformationListener* )
  extends TransformationFactory( listeners : _* ) {
  val LetInExplicitOnce : Transformation = listenTo {
    case OperEx( oper : LetInOper, body ) =>

      /** Make a fresh temporary DB, store all decls inside */
      val bodyDB = BodyDBFactory.makeDBFromDecls( oper.defs )

      /**
        * Inline as if operators were external.
        */
      InlineFactory( bodyDB, listeners : _* ).InlineAll( body )
    case ex => ex
  }

  private def lambda( ex : TlaEx ) : TlaEx = {
    val post = LetInExplicitOnce( ex )
    if ( post == ex ) ex else lambda( post )
  }

  /**
    * Recursive call to LetInExplicitOnce is needed because LET-IN may be nested
    */
  val LetInExplicitAllToplevel : Transformation = listenTo {
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
  val AllLetInExplicit : Transformation =
    new RecursiveTransformation( LetInExplicitAllToplevel )
}
