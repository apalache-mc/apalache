package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.ArenaCell
import at.forsyte.apalache.tla.types.tla

/**
 * Contains miscellaneous methods related to [[ElemPtr]]s.
 *
 * @author
 *   Jure Kukovec
 */
object PtrUtil {

  // If a set cell points to an element cell via multiple pointers, and at least one of them is fixed,
  // the representation can be simplified such that only the fixed pointer edge remains.
  // Otherwise, instead of pointers p1,...,pn has-conditions c1,...,cn, we can use a single pointer with a
  // has-condition c1 \/ ... \/ cn.
  def mergePtrs(cell: ArenaCell, ptrs: Seq[ElemPtr]): ElemPtr = {
    require(ptrs.forall(_.elem == cell))
    ptrs match {
      case Seq(single) => single
      case _ =>
        if (ptrs.exists { _.isInstanceOf[FixedElemPtr] }) FixedElemPtr(cell)
        else SmtExprElemPtr(cell, tla.or(ptrs.map(_.toSmt): _*))
    }
  }

}
