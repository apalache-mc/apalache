package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

class Reordering[T]( ord : Ordering[T], rankingFn : TlaEx => T, tracker : TransformationTracker ) {

  def reorder : TlaExTransformation = tracker.track {
    // For now, only /\ and \/ are reordered, but the same process works for all commutative operators
    case ex@OperEx( op@( TlaBoolOper.and | TlaBoolOper.or ), args@_* ) =>
      val reorderedArgs = args.sortBy( rankingFn )( ord ) map reorder
      if ( args == reorderedArgs ) ex
      else OperEx( op, reorderedArgs : _* )

    case ex@OperEx( op, args@_* ) =>
      val newArgs = args map reorder
      if ( args == newArgs ) ex
      else OperEx( op, newArgs : _* )

    case ex@LetInEx( letInBody, defs@_* ) =>
      val newDefs = defs map {
        // Assignments can only appear in nullary operators
        case TlaOperDecl( name, Nil, declBody ) =>
          TlaOperDecl( name, Nil, reorder( declBody ) )
        case d => d
      }
      val newBody = reorder( letInBody )
      if ( defs == newDefs && letInBody == newBody ) ex
      else LetInEx( newBody, newDefs : _* )


    case ex => ex

  }
}

object Reordering {

  // The order we want, for x < y, is Some(x) < Some(y) < None
  object IntOptOrdering extends Ordering[Option[Int]] {
    def compare( x : Option[Int], y : Option[Int] ) : Int = (x, y) match {
      case (Some( xVal ), Some( yVal )) => Ordering[Int].compare( xVal, yVal )
      case (None, Some( _ )) => 1
      case (Some( _ ), None) => -1
      case _ => 0
    }
  }

}
