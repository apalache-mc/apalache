package at.forsyte.apalache.tla.lir.storage


import at.forsyte.apalache.tla.lir.oper.LetInOper
import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, UID}
import com.google.inject.Singleton

import scala.collection.mutable

/**
  * ChangeListener tracks predecessors of expressions;
  *
  * If a transformation takes ex1 with UID x as input and returns ex2 with UID y and x != y, then
  * ChangeListener will contain y -> x.
  */
@Singleton
class ChangeListener extends TransformationListener {
  private val map = new mutable.HashMap[UID, UID]()

  private def conditionalInsert(ex: TlaEx, uid: UID): Unit =
    if (!map.contains(ex.ID) && ex.ID != uid)
      map.update( ex.ID, uid )

  // Sometimes, a transformation will create a complex expression from a simple one,
  // e.g. UNCHANGED x -> x' \in {x}
  // In these cases, we treat every subexpression of the resulting complex expression
  // as if it were produced by an anonymous transformation from the original
  private def inheritUID(ex: TlaEx, uid: UID) : Unit = {
    ex match {
      case OperEx( letIn : LetInOper, body ) =>
        letIn.defs map {
          _.body
        } foreach {
          inheritUID( _, uid )
        }
        inheritUID( body, uid )
      case OperEx( _, args@_* ) =>
        args foreach {
          inheritUID( _, uid )
        }
      case _ => // noop
    }
    conditionalInsert( ex, uid )
  }

  override def onTransformation( originEx : TlaEx, newEx : TlaEx ) : Unit = {
    if ( originEx.ID != newEx.ID ) {
      map.update( newEx.ID, originEx.ID )
      inheritUID( newEx, originEx.ID )
    }
  }

  def traceBack( p_id : UID ) : UID = map.get( p_id ) match {
    case Some( id ) => traceBack( id )
    case _ => p_id
  }
}
