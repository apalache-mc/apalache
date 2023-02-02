package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.{ElemPtr, PtrUtil}
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.types.tla
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.{OperEx, SetT1, TypingException}
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction

/**
 * Implements the rule for a union of all set elements, that is, UNION S for a set S that contains sets as elements.
 *
 * @author
 *   Igor Konnov
 */
class SetUnionRule(rewriter: SymbStateRewriter) extends RewritingRule {

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.union, _) => true
      case _                           => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.union, topSet) =>
        // rewrite the arguments into memory cells
        var nextState = rewriter.rewriteUntilDone(state.setRex(topSet))
        val topSetCell = nextState.asCell
        val elemType =
          topSetCell.cellType match {
            case CellTFrom(SetT1(SetT1(et))) =>
              et

            case _ =>
              throw new TypingException(s"Applying UNION to $topSet of type ${topSetCell.cellType}", state.ex.ID)
          }

        val sets = Set(nextState.arena.getHas(topSetCell): _*).toList // remove duplicates too
        val elemsOfSets = sets.map { s => s -> nextState.arena.getHasPtr(s) }

        // We map each cell, which appears in some set, to all of the pointers pointing to it, and
        // all the sets containing it
        val (cellMap, pointingSetMap) =
          elemsOfSets.foldLeft(Map.empty[ArenaCell, Seq[ElemPtr]], Map.empty[ArenaCell, Set[ArenaCell]]) {
            case ((partialCellMap, partialPointingSet), (setCell, setElemPtrs)) =>
              setElemPtrs.foldLeft((partialCellMap, partialPointingSet)) {
                case ((innerPartialCellMap, innerPartialPointingSet), ptr) =>
                  val elem = ptr.elem
                  // ptr is one of the pointers pointing at elem
                  val newCellMapAtElem = elem -> (innerPartialCellMap.getOrElse(elem, Seq.empty) :+ ptr)
                  // setCell is one of the cells for which one of its has-edges (i.e. ptr) points at elem
                  val newPointingSetAtElem = elem -> (innerPartialPointingSet.getOrElse(elem, Set.empty) + setCell)
                  (innerPartialCellMap + newCellMapAtElem, innerPartialPointingSet + newPointingSetAtElem)
              }
          }

        // Fixed pointers dominate, if no pointer is fixed we take the disjunction of the smt constraints
        val unionElemPtrs: Seq[ElemPtr] = cellMap.toSeq.map { case (cell, ptrs) =>
          PtrUtil.mergePtrs(cell, ptrs)
        }

        // introduce a set cell
        nextState = nextState.updateArena(_.appendCell(SetT1(elemType)))
        val newSetCell = nextState.arena.topCell

        if (unionElemPtrs.isEmpty) {
          // just return an empty set
          // TODO: cache empty sets!
          nextState.setRex(newSetCell.toNameEx)
        } else {
          // add all the elements to the arena
          nextState = nextState.updateArena(_.appendHas(newSetCell, unionElemPtrs: _*))

          def inPointingSet(elemCell: ArenaCell, set: ArenaCell): TBuilderInstruction = {
            // this is sound, because we have generated element equalities
            // and thus can use congruence of in(...) for free
            tla.and(tla.selectInSet(set.toBuilder, topSetCell.toBuilder),
                tla.selectInSet(elemCell.toBuilder, set.toBuilder))
          }

          // Require each cell to be in one of the sets, e.g., consider UNION { {1} \ {1}, {1} }
          // Importantly, when elemCell is pointed by several sets S_1, .., S_k, we require:
          //    in(elemCell, newSetCell)
          //      <=> in(elemCell, S_1) /\ in(S_1, topSetCell) \/ ... \/ in(elemCell, S_k) /\ in(S_k, topSetCell)
          //
          // This approach is more expensive at the rewriting phase, but it produces O(n) constraints in SMT,
          // in contrast to the old approach with equalities and uninterpreted functions, which required O(n^2) constraints.
          // TODO: drop assertGroundExpr: #2384
          unionElemPtrs.foreach { elemPtr =>
            val elemCell = elemPtr.elem
            val pointingSets = pointingSetMap.getOrElse(elemCell, Set.empty).toList
            assert(pointingSets.nonEmpty)
            val existsIncludingSet = tla.or(pointingSets.map(inPointingSet(elemCell, _)): _*)
            val inUnionSet = tla.storeInSet(elemCell.toBuilder, newSetCell.toBuilder)
            val notInUnionSet = tla.storeNotInSet(elemCell.toBuilder, newSetCell.toBuilder)
            val ite = tla.ite(existsIncludingSet, inUnionSet, notInUnionSet)
            rewriter.solverContext.assertGroundExpr(ite)
          }

          // that's it
          nextState.setRex(newSetCell.toNameEx)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }
}
