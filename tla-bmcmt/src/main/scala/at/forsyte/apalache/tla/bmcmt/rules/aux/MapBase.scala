package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.IntTupleIterator
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

/**
  * The base rules for a set map {e : x ∈ S}. This class was extracted from SetMapRule, as it was used in other rules
  * that are now obsolete. Due to the general nature of this mapping, we keep it in a separate class.
  *
  * @param rewriter the symbolic rewriter
  * @author Igor Konnov
  */
class MapBase(rewriter: SymbStateRewriter) {
  /**
   <p>Implement a mapping { e: x_1 ∈ S_1, ..., x_n ∈ S_n }.</p>

   <p>This implementation computes the cross product and maps every cell using the map expression.
    It is not truly symbolic, we have to find a better way.</p>
    */
  def rewriteSetMapManyArgs(state: SymbState,
                            mapEx: TlaEx,
                            varNames: Seq[String],
                            setEs: Seq[TlaEx]): SymbState = {
    // first, rewrite the variable domains S_1, ..., S_n
    var (nextState, sets) = rewriter.rewriteSeqUntilDone(state.setTheory(CellTheory()), setEs)
    def findSetCellAndElemType(setCell: ArenaCell): (ArenaCell, CellT) = {
      setCell.cellType match {
        case FinSetT(elemType) =>
          (setCell, elemType)

        case tp @ _ => throw new NotImplementedError("A set map over %s is not implemented".format(tp))
      }
    }

    val (setsAsCells, elemTypes) = (sets.map(nextState.arena.findCellByNameEx) map findSetCellAndElemType).unzip
    val elemsOfSets = setsAsCells.map(nextState.arena.getHas)
    val setLimits = elemsOfSets.map(_.size - 1)
    // find the types of the target expression and of the target set
    val targetMapT = rewriter.typeFinder.computeRec(mapEx)
    val targetSetT = FinSetT(targetMapT)

    nextState = nextState.updateArena(_.appendCell(targetSetT))
    val resultSetCell = nextState.arena.topCell

    // enumerate all possible indices and map the corresponding tuples to cells
    def byIndex(indices: Seq[Int]): Seq[ArenaCell] =
      elemsOfSets.zip(indices) map Function.tupled { (s, i) => s(i) }

    val tupleIter = new IntTupleIterator(setLimits).map(byIndex)

    // the SMT constraints are added right in the method
    val (newState, resultElemCells) =
      mapCellsManyArgs(nextState, resultSetCell, mapEx, varNames, setsAsCells, tupleIter)

    // that's it
    val finalState =
      newState.setTheory(CellTheory())
        .setRex(resultSetCell.toNameEx)
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
    var nextState = rewriter.rewriteUntilDone(mapState)
    val mapResultCell = nextState.asCell

    // require each new cell to be in the new set iff the old cell was in the old set
    val inNewSet = OperEx(TlaSetOper.in, mapResultCell.toNameEx, targetSetCell.toNameEx)
    def inSourceSet(arg: ArenaCell, set: ArenaCell) = OperEx(TlaSetOper.in, arg.toNameEx, set.toNameEx)
    val argsInSourceSets = tla.and(valuesAsCells.zip(setsAsCells) map (inSourceSet _).tupled :_*)
    val ifAndOnlyIf = OperEx(TlaOper.eq, inNewSet, argsInSourceSets)
    // add the edge before adding the constraint
    nextState = nextState.updateArena(_.appendHas(targetSetCell, mapResultCell))
    rewriter.solverContext.assertGroundExpr(ifAndOnlyIf)

    (nextState.setBinding(state.binding), mapResultCell) // reset the binding and return the result
  }
}
