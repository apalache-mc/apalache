package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.IntTupleIterator
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * The base rules for set mappings: {e : x ∈ S}, S_1 × ... × S_n, [a_1 ↦ S_1, ..., a_n ↦ S_n]
  *
  * @param rewriter the symbolic rewriter
  * @param isBijective a hint that the mapping is bijective,
  *    e.g., as in { &lt;&lt;x, y&gt;&gt; : x ∈ S_1, y ∈ S_ 2}, so the additional constraints are not required.
  * @author Igor Konnov
  */
class MapBase(rewriter: SymbStateRewriter, val isBijective: Boolean) {

  /**
   <p>Implement a mapping { e: x_1 ∈ S_1, ..., x_n ∈ S_n }.</p>

   <p>This implementation computes the cross product and maps every cell using the map expression.
    It is not truly symbolic, we have to find a better way.</p>
    */
  def rewriteSetMapManyArgs(state: SymbState,
                            mapEx: TlaEx,
                            varNames: Seq[String],
                            setEs: Seq[TlaEx]): SymbState = {
    // TODO: this translation is not sound when several values are actually mapped to the same value.
    // first, rewrite the variable domains S_1, ..., S_n
    val (setState, sets) = rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), setEs)
    val setsAsCells = sets map setState.arena.findCellByNameEx
    def getSetElemType(c: ArenaCell) = c.cellType match {
      case FinSetT(et) => et
      case t@_ => throw new RewriterException("Expected a finite set, found: " + t)
    }
    val setElemTypes = setsAsCells map getSetElemType
    val elemsOfSets = setsAsCells.map(setState.arena.getHas)
    val setLimits = elemsOfSets.map(_.size - 1)
    // find the type of the target expression and of the target set
    val targetMapT = rewriter.typeFinder.computeRec(mapEx)
    val argTypes = 0.until(2 * setsAsCells.size) map
      { i => if (i % 2 == 0) setElemTypes(i / 2) else setsAsCells(i / 2).cellType }
    val targetSetT = rewriter.typeFinder.compute(state.ex, targetMapT +: argTypes :_*)

    val arena = setState.arena.appendCell(targetSetT)
    val resultSetCell = arena.topCell

    // enumerate all possible indices and map the corresponding tuples to cells
    def byIndex(indices: Seq[Int]): Seq[ArenaCell] =
      elemsOfSets.zip(indices) map Function.tupled { (s, i) => s(i) }

    val tupleIter = new IntTupleIterator(setLimits).map(byIndex)
    // the SMT constraints are added right in the method
    val (newState, resultElemCells) =
      mapCellsManyArgs(setState.setArena(arena), resultSetCell, mapEx, varNames, setsAsCells, tupleIter)

    // bind the element cells to the set
    val newArena = resultElemCells.foldLeft(newState.arena) {(a, e) => a.appendHas(resultSetCell, e)}

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setArena(newArena).setRex(resultSetCell.toNameEx)
    rewriter.coerce(finalState, state.theory)
  }

  private def mapCellsManyArgs(state: SymbState,
                               targetSetCell: ArenaCell,
                               mapEx: TlaEx,
                               varNames: Seq[String],
                               setsAsCells: Seq[ArenaCell],
                               cellsIter: Iterator[Seq[ArenaCell]]): (SymbState, Seq[ArenaCell]) = {
    // we could have done it with foldLeft, but that would be even less readable
    var newState = state
    var resultCells: Seq[ArenaCell] = Seq()
    while (cellsIter.hasNext) {
      val argCells = cellsIter.next()
      val (ns, resultCell) = mapCellsManyArgsOnce(newState, targetSetCell, mapEx, varNames, setsAsCells, argCells)
      newState = ns
      resultCells :+= resultCell
    }

    (newState, resultCells.distinct)
  }

  private def mapCellsManyArgsOnce(state: SymbState,
                                   targetSetCell: ArenaCell,
                                   mapEx: TlaEx,
                                   varNames: Seq[String],
                                   setsAsCells: Seq[ArenaCell],
                                   valuesAsCells: Seq[ArenaCell]): (SymbState, ArenaCell) = {
    // bind the variables to the corresponding cells
    val newBinding: Binding = varNames.zip(valuesAsCells).foldLeft(state.binding)((m, p) => m + p)
    val mapState = state.setTheory(CellTheory()).setBinding(newBinding).setRex(mapEx)
    val newState = rewriter.rewriteUntilDone(mapState)
    val mapResultCell = newState.arena.findCellByNameEx(newState.ex)

    // require each new cell to be in the new set iff the old cell was in the old set
    val inNewSet = OperEx(TlaSetOper.in, mapResultCell.toNameEx, targetSetCell.toNameEx)
    def inSourceSet(arg: ArenaCell, set: ArenaCell) = OperEx(TlaSetOper.in, arg.toNameEx, set.toNameEx)
    val argsInSourceSets = tla.and(valuesAsCells.zip(setsAsCells) map (inSourceSet _).tupled :_*)
    val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, argsInSourceSets)
    rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)

    (newState.setBinding(state.binding), mapResultCell) // reset the binding and return the result
  }
}
