package at.forsyte.apalache.tla.bmcmt.arena

import at.forsyte.apalache.tla.bmcmt.{ArenaCell, ElemPtr, FixedElemPtr, SmtExprElemPtr}
import at.forsyte.apalache.tla.types.{tlaU => tla}

/**
 * Contains miscellaneous methods related to [[ElemPtr]]s.
 *
 * @author
 *   Jure Kukovec
 */
object PtrUtil {

  /**
   * Maps each cell, which appears in some set, to all of the pointers pointing to it. Simpler version of
   * `getCellAndPointingSetMaps`, when pointing sets aren't needed.
   */
  def getCellMap(ptrs: Seq[ElemPtr]): Map[ArenaCell, Seq[ElemPtr]] =
    ptrs.foldLeft(Map.empty[ArenaCell, Seq[ElemPtr]]) { case (m, ptr) =>
      val elem = ptr.elem
      m + (elem -> (m.getOrElse(elem, Seq.empty) :+ ptr))
    }

  /**
   * Maps each cell, which appears in some set, to all of the pointers pointing to it, and all the sets containing it.
   */
  def getCellAndPointingSetMaps(
      elemsOfSets: Seq[(ArenaCell, Seq[ElemPtr])]): (Map[ArenaCell, Seq[ElemPtr]], Map[ArenaCell, Set[ArenaCell]]) =
    elemsOfSets.foldLeft(Map.empty[ArenaCell, Seq[ElemPtr]], Map.empty[ArenaCell, Set[ArenaCell]]) {
      case ((partialCellMap, partialPointingSetMap), (setCell, setElemPtrs)) =>
        setElemPtrs.foldLeft((partialCellMap, partialPointingSetMap)) {
          case ((innerPartialCellMap, innerPartialPointingSet), ptr) =>
            val elem = ptr.elem
            // ptr is one of the pointers pointing at elem
            val newCellMapAtElem = elem -> (innerPartialCellMap.getOrElse(elem, Seq.empty) :+ ptr)
            // setCell is one of the cells for which one of its has-edges (i.e. ptr) points at elem
            val newPointingSetAtElem = elem -> (innerPartialPointingSet.getOrElse(elem, Set.empty) + setCell)
            (innerPartialCellMap + newCellMapAtElem, innerPartialPointingSet + newPointingSetAtElem)
        }
    }

  // If a set cell points to an element cell via multiple pointers, and at least one of them is fixed,
  // the representation can be simplified such that only the fixed pointer edge remains.
  // Otherwise, instead of pointers p1,...,pn has-conditions c1,...,cn, we can use a single pointer with a
  // has-condition c1 \/ ... \/ cn.
  def mergePtrs(cell: ArenaCell, ptrs: Seq[ElemPtr]): ElemPtr = {
    require(ptrs.forall(_.elem == cell))
    ptrs match {
      case Seq(single) => single
      case _           =>
        if (ptrs.exists { _.isInstanceOf[FixedElemPtr] }) FixedElemPtr(cell)
        else SmtExprElemPtr(cell, tla.or(ptrs.map(_.toSmt): _*))
    }
  }

  // Sequentially combines getCellMap and mergePtrs
  def mergePtrsByCellMap(ptrs: Seq[ElemPtr]): Seq[ElemPtr] = getCellMap(ptrs).toSeq.map { case (cell, ps) =>
    mergePtrs(cell, ps)
  }

  def samePointer(original: ElemPtr): ArenaCell => ElemPtr = original match {
    case _: FixedElemPtr          => FixedElemPtr
    case SmtExprElemPtr(_, smtEx) => SmtExprElemPtr(_, smtEx)
  }

  // When looking at cartesian product sets (e.g. for Map), the following holds true:
  // If c_S represents S, c_a represents a, c_T represents T, c_b represents b, c_ST represents S x T
  // and c_tup represents <<a,b>>, then
  // c_ST has a fixed pointer to c_tup <=> c_S has a fixed pointer to c_a, and c_T has a fixed pointer to c_b
  // In all other cases, c_ST has a SmtExprElemPtr(expr) to c_tup, where expr is the conjunction of the expressions held
  // by the pointer of c_S to c_a and the pointer of c_T to c_b.
  def tuplePtr(setElemPtrs: Seq[ElemPtr]): ArenaCell => ElemPtr = {
    require(setElemPtrs.nonEmpty)
    if (setElemPtrs.forall(_.isInstanceOf[FixedElemPtr]))
      FixedElemPtr
    else
      SmtExprElemPtr(_, tla.and(setElemPtrs.map(_.toSmt): _*))
  }

}
