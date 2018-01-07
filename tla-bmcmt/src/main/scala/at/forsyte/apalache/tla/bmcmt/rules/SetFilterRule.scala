package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, UnknownT}
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, NullEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-SET-FILTER[1-2].
  *
  * @author Igor Konnov
  */
class SetFilterRule(rewriter: SymbStateRewriter) extends RewritingRule {
  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.filter, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.filter, NameEx(varName), setEx, predEx) =>
        // rewrite the set expression into a memory cell
        val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
        val setCell = setState.arena.findCellByNameEx(setState.ex)
        val elemType =
          setCell.cellType match {
            case FinSetT(et) => et
            case _ =>
              throw new RewriterException("Expression %s evaluates to a non-set cell %d"
                .format(setEx.toString, setCell.id))
          }
        // unfold the set and produce boolean constants for every potential element
        val potentialCells = setState.arena.getHas(setCell)
        // similar to SymbStateRewriter.rewriteSeqUntilDone, but also handling exceptions
        var newState = setState

        def eachElem(potentialCell: ArenaCell): TlaEx = {
          // add [cell/x]
          val newBinding = newState.binding + (varName -> potentialCell)
          val cellState = new SymbState(predEx, BoolTheory(), newState.arena, newBinding)
          try {
            val ns = rewriter.rewriteUntilDone(cellState)
            newState = ns.setBinding(ns.binding - varName) // reset binding
            ns.ex
          } catch {
            case ub: UndefinedBehaviorError =>
              newState = newState.setArena(ub.arena) // something was added to the arena
              NullEx // accessing a non-existent record field => filter out, that is, return NullEx
          }
        }

        // compute predicates for all the cells, some may statically result in NullEx
        val computedPreds: Seq[TlaEx] = potentialCells map eachElem
        val filteredCellsAndPreds = (potentialCells zip computedPreds) filter (_._2 != NullEx)
        // Importantly, we unified the types of cells that were not statically filtered out.
        // In case of records, it means that the type is unified to those records
        // that do not statically violate the predicate.
        val unifier =
          if (filteredCellsAndPreds.isEmpty) {
            Some(UnknownT())
          } else {
            types.unify(filteredCellsAndPreds.map(_._1.cellType): _*)
          }

        if (unifier.isEmpty) {
          throw new TypeException("No type unifier for the elements of: " + setEx)
        }

        // introduce a new set
        val arena = newState.arena.appendCell(FinSetT(unifier.get))
        val newSetCell = arena.topCell
        val newArena = filteredCellsAndPreds.map(_._1)
          .foldLeft(arena) ((a, e) => a.appendHas(newSetCell, e))

        // require each cell to satisfy the predicate
        def addCellCons(cell: ArenaCell, pred: TlaEx): Unit = {
          val inNewSet = OperEx(TlaSetOper.in, cell.toNameEx, newSetCell.toNameEx)
          val inOldSet = OperEx(TlaSetOper.in, cell.toNameEx, setCell.toNameEx)
          val inOldSetAndPred = OperEx(TlaBoolOper.and, pred, inOldSet)
          val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, inOldSetAndPred)
          rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)
        }

        // add SMT constraints
        for ((cell, pred) <- filteredCellsAndPreds)
          addCellCons(cell, pred)

        val finalState =
          newState.setTheory(CellTheory())
            .setArena(newArena).setRex(newSetCell.toNameEx)
        rewriter.coerce(finalState, state.theory) // coerce to the source theory

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }
}
