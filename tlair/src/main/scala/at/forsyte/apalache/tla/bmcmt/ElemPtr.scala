package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.types.{tlaU => tla, BuilderUT => BuilderT}

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
  def toSmt: BuilderT

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
  def restrict(cond: BuilderT): SmtExprElemPtr
}

/**
 * An element pointer that always evaluates to true. This pointer is used to encode that the element unconditionally
 * belongs to a set. For example, when constructing the set `{ 1, 2, 3 }`.
 *
 * @param elem
 *   the element this pointer is pointing to.
 */
case class FixedElemPtr(elem: ArenaCell) extends ElemPtr {
  override def toSmt: BuilderT = tla.bool(true)

  override def restrict(cond: BuilderT): SmtExprElemPtr = SmtExprElemPtr(elem, cond)
}

/**
 * An element pointer whose value is encoded via an SMT expression. For instance, it can be used to join memberships of
 * two sets: `(and in_123_S in_124_T)`.
 *
 * @param elem
 *   the element this pointer is pointing to.
 * @param smtEx
 *   the corresponding SMT expression.
 */
case class SmtExprElemPtr(elem: ArenaCell, smtEx: BuilderT) extends ElemPtr {
  override def toSmt: BuilderT = smtEx
  def restrict(cond: BuilderT): SmtExprElemPtr = this.copy(smtEx = tla.and(smtEx, cond))
}
