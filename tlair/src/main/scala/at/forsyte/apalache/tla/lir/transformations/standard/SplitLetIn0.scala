package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetIn0Ex, OperEx}
import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

object SplitLetIn0 {
  private def splitLetIn( tracker : TransformationTracker ) : TlaExTransformation = tracker.track {
    case OperEx( oper : LetInOper, body ) =>

      val (arity0, arityGt0) = oper.defs.partition( _.formalParams.isEmpty )

      /** Let-in may be nested */
      val splitInBody = apply( tracker )( body )

      /** We assume that the operators are parser-ordered correctly, so that
        *
        * LET A1 == ...
        *     ...
        *     An == ...
        * IN X
        *
        * is equivalent to
        *
        * LET A1 == ...
        * IN (LET A2 == ... IN (... LET An == ... IN X))
        */
      val zeroForm = arity0.foldRight( splitInBody ){
        case (decl, b) => LetIn0Ex( decl.name, decl.body, b )
      }

      if ( arityGt0.isEmpty )
        zeroForm
      else {
        val newOper = new LetInOper( arityGt0 )
        OperEx( newOper, zeroForm )
      }
    case ex => ex
  }

  /**
    * Returns a transformation which replaces all 0-arity LET-IN defined expressions with
    * the LetIn0Ex syntax.
    *
    * Example:
    * LET X(a) == a + x
    * Y == 1
    * IN X(0) > Y
    * -->
    * LET X(a) == a + x
    * IN LetIn0Ex( "Y", 1, X(0) > Y)
    */
  def apply( tracker : TransformationTracker ) : TlaExTransformation = tracker.track { ex =>
    val tr = splitLetIn( tracker )
    lazy val self = apply( tracker )
    ex match {
      case OperEx( op : LetInOper, _ ) =>
        tr( ex )
      case LetIn0Ex( name, operBody, exprBody ) =>
        val newOperBody = self(operBody)
        val newExprBody = self(exprBody)
        val newEx =
          if ( newOperBody == operBody && newExprBody == exprBody ) ex
          else LetIn0Ex(name, newOperBody, newExprBody)
        tr( newEx )
      case ex@OperEx( op, args@_* ) =>
        val newArgs = args map self
        val retEx = if ( args == newArgs ) ex else OperEx( op, newArgs : _* )
        tr( retEx )
      case _ => tr( ex )
    }
  }
}

