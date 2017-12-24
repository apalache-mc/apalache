package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types.FinSetT
import at.forsyte.apalache.tla.lir.oper.{TlaBoolOper, TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

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
        // similar to SymbStateRewriter.rewriteSeqUntilDone
        def process(st: SymbState, seq: Seq[ArenaCell]): (SymbState, Seq[TlaEx]) = {
          seq match {
            case Seq() =>
              (st, List())

            case (cell: ArenaCell) :: tail =>
              val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
              val newBinding = ts.binding + (varName -> cell)
              val cellState = new SymbState(predEx, BoolTheory(), ts.arena, newBinding)
              // add [cell/x]
              val ns = rewriter.rewriteUntilDone(cellState)
              (ns.setBinding(ts.binding), ns.ex :: nt) // reset binding and add the new expression to the tail
          }
        }

        // compute predicates for all the cells
        val (newState: SymbState, newPreds: Seq[TlaEx]) = process(setState, potentialCells)
        // introduce a new set
        val arena = newState.arena.appendCell(FinSetT(elemType))
        val newSetCell = arena.topCell
        val newArena = potentialCells.foldLeft(arena)((a, e) => a.appendHas(newSetCell, e))

        // require each cell to satisfy the predicate
        def addCellCons(cell: ArenaCell, pred: TlaEx): Unit = {
          val inNewSet = OperEx(TlaSetOper.in, cell.toNameEx, newSetCell.toNameEx)
          val inOldSet = OperEx(TlaSetOper.in, cell.toNameEx, setCell.toNameEx)
          val inOldSetAndPred = OperEx(TlaBoolOper.and, pred, inOldSet)
          val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, inOldSetAndPred)
          rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)
        }

        // add SMT constraints
        for ((cell, pred) <- potentialCells zip newPreds)
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
