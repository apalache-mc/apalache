package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{BoolT1, TlaEx, UID}

/**
 * An abstract membership pointer.
 */
sealed trait ElemPtr {

  /**
   * Get the element that this edge is pointing to.
   * @return
   *   an arena cell that is pointed by this pointer
   */
  def elem: ArenaCell

  /**
   * Translate the membership test into an expression that can be understood by Z3SolverContext.
   */
  def toSmt: TlaEx
}

/**
 * An element pointer that always evaluates to a fixed Boolean value.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param value
 *   the value (false or true).
 */
case class FixedElemPtr(elem: ArenaCell, value: Boolean) extends ElemPtr {
  override def toSmt: TlaEx = {
    tla.bool(value).as(BoolT1())
  }
}

/**
 * An element pointer whose value is encoded as a Boolean constant. Its value is found by the SMT solver.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param id
 *   the unique id of the pointer.
 */
case class SmtConstElemPtr(elem: ArenaCell, id: UID) extends ElemPtr {
  val uniqueName = s"_bool_elem$id"

  override def toSmt: TlaEx = {
    tla.name(uniqueName).as(BoolT1())
  }
}

/**
 * An element pointer whose value is encoded via an SMT expression.
 * @param elem
 *   the element this pointer is pointing to.
 * @param smtEx
 *   the corresponding SMT expression.
 */
case class SmtExprElemPtr(elem: ArenaCell, smtEx: TlaEx) extends ElemPtr {
  override def toSmt: TlaEx = smtEx
}
