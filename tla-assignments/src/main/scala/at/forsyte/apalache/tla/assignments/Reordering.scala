package at.forsyte.apalache.tla.assignments

import at.forsyte.apalache.tla.lir.oper.TlaBoolOper
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaEx, TlaOperDecl}
import at.forsyte.apalache.tla.lir.transformations.{TlaExTransformation, TransformationTracker}

/**
  * `Reordering` allows us to change the order of arguments passed to commutative operators (e.g. /\).
  * This helps enforce a notion of, for example, left-to-right processing of arguments (like in TLC), which
  * matters in variable assignments, which should always (syntactically) precede variable use cases.
  * @param ord An ordering over `T`
  * @param rankingFn Assigns a value in `T` to each `TlaEx`. This indirectly defines an ordering on `TlaEx`:
  *                  e1 <= e2 iff ord.le( rankingFn(e1), rankingFn(e2) ) etc.
  * @param tracker A transformation tracker.
  * @tparam T An orderable domain. Default: Option[Int]
  */
class Reordering[T]( ord : Ordering[T], rankingFn : TlaEx => T, tracker : TransformationTracker ) {

  def reorder : TlaExTransformation = tracker.track {
    // For now, both /\ and \/ are reordered
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
  // The reason is, each assignment candidate `e` maps to a value of the shape Some(f(e)),
  // where f is a witness to the acyclicity property, while a non-assignment `e` maps either to None
  // or to Some(min{ f(e2) | e2 is an assignment candidate and a subexpression of e})
  // Reordering with this Ordering pushes assignments to the front at each nesting level and preserves their relative order,
  // as defined by f.
  object IntOptOrdering extends Ordering[Option[Int]] {
    def compare( x : Option[Int], y : Option[Int] ) : Int = (x, y) match {
      case (Some( xVal ), Some( yVal )) => Ordering[Int].compare( xVal, yVal )
      case (None, Some( _ )) => 1
      case (Some( _ ), None) => -1
      case _ => 0
    }
  }

}
