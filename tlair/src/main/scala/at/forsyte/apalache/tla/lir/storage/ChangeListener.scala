package at.forsyte.apalache.tla.lir.storage

import at.forsyte.apalache.tla.lir.transformations.TransformationListener
import at.forsyte.apalache.tla.lir.{LetInEx, OperEx, TlaDecl, TlaEx, UID}
import com.google.inject.Singleton

import scala.collection.mutable

/**
  * ChangeListener tracks predecessors of expressions;
  *
  * If a transformation takes ex1 with UID x as input and returns ex2 with UID y and x != y, then
  * ChangeListener will record y -> x. Moreover, if ex2 contains a subexpression g2 that is not tracked
  * by ChangeListener (and none of its ascendants but ex2 is tracked), then ChangeListener will record g2 -> ex1.
  *
  * TODO: Igor @ 11.08.2019, the name 'ChangeListener' sounds similar to 'TransformationListener'.
  * Shall we give a better name, for instance, PredIdSavingListener?
  *
  * TODO: Igor @ 11.08.2019, we are using Map[UID, UID] to record the changes between the subtrees.
  * There must be a less wasteful data structure for that.
  *
  * @author Jure Kukovec
  */
@Singleton
class ChangeListener extends TransformationListener {
  private val map = new mutable.HashMap[UID, UID]()

  private def conditionalInsert(ex: TlaEx, uid: UID): Unit =
    if (!map.contains(ex.ID) && ex.ID != uid)
      map.update(ex.ID, uid)

  // Sometimes, a transformation will create a complex expression from a simple one,
  // e.g. UNCHANGED x -> x' \in {x}
  // In these cases, we treat every subexpression of the resulting complex expression
  // as if it were produced by an anonymous transformation from the original
  private def inheritUID(ex: TlaEx, uid: UID): Unit = {
    ex match {
      case LetInEx(body, defs @ _*) =>
        defs map {
          _.body
        } foreach {
          inheritUID(_, uid)
        }
        inheritUID(body, uid)

      case OperEx(_, args @ _*) =>
        args foreach {
          inheritUID(_, uid)
        }
      case _ => // noop
    }
    conditionalInsert(ex, uid)
  }

  override def onTransformation(originEx: TlaEx, newEx: TlaEx): Unit = {
    if (originEx.ID != newEx.ID) {
      map.update(newEx.ID, originEx.ID)
      inheritUID(newEx, originEx.ID)
    }
  }

  override def onDeclTransformation(
      originalDecl: TlaDecl,
      newDecl: TlaDecl
  ): Unit = {
    if (originalDecl.ID != newDecl.ID) {
      map.update(newDecl.ID, originalDecl.ID)
    }
  }

  /**
    * Is identifier p_id registered as a result of translation?
    *
    * @param p_id expression identifier
    * @return true, if p_id has been registered
    */
  def isDefinedAt(p_id: UID): Boolean = {
    map.isDefinedAt(p_id)
  }

  def traceBack(p_id: UID): UID =
    map.get(p_id) match {
      case Some(id) => traceBack(id)
      case _        => p_id
    }
}
