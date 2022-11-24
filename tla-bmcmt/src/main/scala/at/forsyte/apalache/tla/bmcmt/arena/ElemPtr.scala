package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.types.tla
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
 * An element pointer that always evaluates to a fixed Boolean value. This pointer is used to encode that the element
 * unconditionally belongs to a set. For example, when constructing the set `{ 1, 2, 3 }`.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param value
 *   the value (false or true).
 */
case class FixedElemPtr(elem: ArenaCell, value: Boolean) extends ElemPtr {
  override def toSmt: TlaEx = {
    tla.bool(value)
  }
}

/**
 * An element pointer whose value is encoded as a Boolean constant. Its value is found by the SMT solver. This pointer
 * is used as a general case, where set membership is completely delegated to SMT. For example, this case class may be
 * used when a set is created non-deterministically with `Gen(n)`.
 *
 * @param elem
 *   the element this pointer is pointing to.
 */
case class SmtConstElemPtr(elem: ArenaCell) extends ElemPtr {

  /**
   * The unique id of the pointer.
   */
  val id: UID = UID.unique

  /**
   * The unique name of the pointer.
   */
  val uniqueName = s"_bool_elem$id"

  override def toSmt: TlaEx = {
    tla.name(uniqueName, BoolT1)
  }
}

/**
 * An element pointer whose value is encoded via an SMT expression. This is a generalization of [[SmtConstElemPtr]]. For
 * instance, it can be used to join memberships of two sets: `(and in_123_S in_124_T)`.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param smtEx
 *   the corresponding SMT expression.
 */
case class SmtExprElemPtr(elem: ArenaCell, smtEx: TlaEx) extends ElemPtr {
  override def toSmt: TlaEx = smtEx
}
