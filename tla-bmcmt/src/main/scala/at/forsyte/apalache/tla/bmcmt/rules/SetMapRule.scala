package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.MapBase
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx}

/**
  * Implements the rules: SE-SET-MAP[1-2].
  *
  * @author Igor Konnov
  */
class SetMapRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val mapbase = new MapBase(rewriter, isBijective = false)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaSetOper.map, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaSetOper.map, mapEx, varsAndSets @ _*) =>
        val varNames = varsAndSets.zipWithIndex.filter(_._2 % 2 == 0).collect { case (NameEx(n), _) => n }
        val sets = varsAndSets.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
        mapbase.rewriteSetMapManyArgs(state, mapEx, varNames, sets)

      case _ =>
        throw new RewriterException("%s is not applicable to %s".format(getClass.getSimpleName, state.ex), state.ex)
    }
  }

  // the old single-argument implementation, will be removed in the future
  private def rewriteSetMap(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx) = {
    // rewrite the set expression into a memory cell
    val setState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(setEx))
    val sourceSetCell = setState.arena.findCellByNameEx(setState.ex)
    val elemT = sourceSetCell.cellType match {
      case FinSetT(et) => et
      case t@_ => throw new RewriterException("Expected a finite set, found: " + t, state.ex)
    }
    // unfold the set and map every potential element to a cell
    val sourceCells = setState.arena.getHas(sourceSetCell)
    // find the type of the target expression and of the target set
    val targetMapT = rewriter.typeFinder.computeRec(mapEx)
    val targetSetT = rewriter.typeFinder.compute(state.ex, targetMapT, elemT, sourceSetCell.cellType)
    // map the source cells using the map expression
    val (newState: SymbState, newCells: Seq[ArenaCell]) =
      mapCells(setState, mapEx, varName, setEx, sourceCells)

    // introduce a new set
    val arena = newState.arena.appendCell(targetSetT)
    val newSetCell = arena.topCell
    val newArena = arena.appendHas(newSetCell, newCells: _*)

    // require each new cell to be in the new set iff the old cell was in the old set
    def addCellCons(oldCell: ArenaCell, newCell: ArenaCell): Unit = {
      val inNewSet = OperEx(TlaSetOper.in, newCell.toNameEx, newSetCell.toNameEx)
      val inOldSet = OperEx(TlaSetOper.in, oldCell.toNameEx, sourceSetCell.toNameEx)
      val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, inOldSet)
      rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)
    }

    // add SMT constraints
    for ((cell, pred) <- sourceCells zip newCells)
      addCellCons(cell, pred)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(newArena).setRex(newSetCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def mapCells(state: SymbState, mapEx: TlaEx, varName: String, setEx: TlaEx, oldCells: Seq[ArenaCell]) = {
    // similar to SymbStateRewriter.rewriteSeqUntilDone and SetFilterRule
    def process(st: SymbState, seq: Seq[ArenaCell]): (SymbState, Seq[TlaEx]) = {
      seq match {
        case Seq() =>
          (st, List())

        case cell :: tail =>
          val (ts: SymbState, nt: List[TlaEx]) = process(st, tail)
          val newBinding = ts.binding + (varName -> cell)
          val cellState = new SymbState(mapEx, CellTheory(), ts.arena, newBinding)
          // add [cell/x]
          val ns = rewriter.rewriteUntilDone(cellState)
          (ns.setBinding(ts.binding), ns.ex :: nt) // reset binding and add the new expression in the head
      }
    }

    // compute mappings for all the cells (some of them may coincide, that's fine)
    val (newState: SymbState, newEs: Seq[TlaEx]) = process(state, oldCells)
    val newCells = newEs.map(newState.arena.findCellByNameEx)
    // Call distinct to remove duplicates, e.g., consider a silly mapping { x \in 1..100 |-> FALSE },
    // which would produce 100 FALSE and they all be mapped to the same cell (by the constant cache)
    (newState, newCells.distinct)
  }
}
