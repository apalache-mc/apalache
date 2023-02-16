package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.lir.{BoolT1, UID}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

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
  def toSmt: TBuilderInstruction

  /**
   * After certain set operations, every pointer must become a SmtExprElemPtr, because the operation invalidates the
   * guarantees of e.g. FixedElemPtr.
   */
  def generalize: SmtExprElemPtr = SmtExprElemPtr(elem, toSmt)

  /**
   * Collection transformations evaluate membership based on original membership _and_ additional restrictions (e.g.
   * filter). `ptr.restrict(x)` returns `ptr2`, such that `ptr2.toSmt` is logically equivalent (but not necessarily
   * syntactically equal) to `tla.and(ptr.toSmt, x)`, while `ptr.elem = ptr2.elem`.
   */
  def restrict(cond: TBuilderInstruction): SmtExprElemPtr
}

/**
 * An element pointer that always evaluates to true. This pointer is used to encode that the element unconditionally
 * belongs to a set. For example, when constructing the set `{ 1, 2, 3 }`.
 *
 * @param elem
 *   the element this pointer is pointing to.
 */
case class FixedElemPtr(elem: ArenaCell) extends ElemPtr {
  override def toSmt: TBuilderInstruction = tla.bool(true)

  override def restrict(cond: TBuilderInstruction): SmtExprElemPtr = SmtExprElemPtr(elem, cond)
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

  override def toSmt: TBuilderInstruction = tla.name(uniqueName, BoolT1)

  // soon-to-be deleted anyway
  override def restrict(cond: TBuilderInstruction): SmtExprElemPtr = SmtExprElemPtr(elem, tla.bool(false))

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
case class SmtExprElemPtr(elem: ArenaCell, smtEx: TBuilderInstruction) extends ElemPtr {
  override def toSmt: TBuilderInstruction = smtEx
  def restrict(cond: TBuilderInstruction): SmtExprElemPtr = this.copy(smtEx = tla.and(smtEx, cond))
}
