package at.forsyte.apalache.tla.lir.transformations.standard

import at.forsyte.apalache.tla.lir.{LetIn0Ex, OperEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

object SplitLetIn0 {

  /** We need to split an ordered collection of OperDecls (from a LET-IN operator),
    * into segments of 0 arity and >0 ariry operators, to replace 0-arity operators with the
    * LetIn0Ex syntax
    */
  private[lir] def collectSegments( decls : Traversable[TlaOperDecl] ) : List[List[TlaOperDecl]] = decls match {
    case d if d.isEmpty => List.empty
    case head :: tail =>
      val rec = collectSegments( tail )
      val headOrEmpty = rec.headOption.getOrElse( List.empty )
      // head has arity >0 && all decls in the first segment have arity >0.
      // if headOption returns None, the 2nd condition vacuously holds for the empty seq
      if ( head.formalParams.nonEmpty && headOrEmpty.forall( _.formalParams.nonEmpty ) )
        ( head +: headOrEmpty ) +: rec.drop( 1 ) // Nil.tail throws, but Nil.drop(1) doesn't
      else
        List( head ) +: rec
  }

  private def splitLetIn( tracker : TransformationTracker ) : TlaExTransformation = tracker.track {
    case OperEx( oper : LetInOper, body ) =>

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
        *
        * Because LET-IN defined operators may reference each other, it's insufficient to
        * simply filter out all 0 arity operators, as this may break the contexts.
        * Instead, we split the oper. declarations into segments.
        */
      val segments = collectSegments( oper.defs )

      // sanity check
      assert( segments.forall { _.nonEmpty } )

      segments.foldRight( splitInBody ) {
        case (decls, b) =>
          // we know decls is nonempty
          val h = decls.head
          if ( h.formalParams.isEmpty )
            LetIn0Ex( h.name, h.body, b )
          else
            OperEx( new LetInOper( decls ), b )

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

