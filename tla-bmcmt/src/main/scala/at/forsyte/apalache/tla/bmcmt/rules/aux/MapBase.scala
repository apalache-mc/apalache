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
  private val typeConvertor = new TypeConverter(rewriter)

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
    // convert the set cell, if required
    def convertIfNeeded(setCell: ArenaCell): ArenaCell = {
      setCell.cellType match {
        case FinSetT(_) =>
          setCell
        case PowSetT(et) =>
          nextState = typeConvertor.convert(nextState.setRex(setCell.toNameEx), FinSetT(et))
          nextState.asCell
        // TODO: convert functions sets too?
        case tp @ _ => throw new NotImplementedError("A set filter over %s is not implemented".format(tp))
      }
    }

    val setsAsCells = sets.map(nextState.arena.findCellByNameEx) map convertIfNeeded

    def getSetElemType(c: ArenaCell) = c.cellType match {
      case FinSetT(et) => et
      case t@_ => throw new RewriterException("Expected a finite set, found %s in %s ".format(t, state.ex), state.ex)
    }
    val setElemTypes = setsAsCells map getSetElemType
    val elemsOfSets = setsAsCells.map(nextState.arena.getHas)
    val setLimits = elemsOfSets.map(_.size - 1)
    // find the type of the target expression and of the target set
    // TODO: types should have been computed already, this was only needed by CartesianProductRule and RecordSetRule
    val targetMapT = rewriter.typeFinder.computeRec(mapEx)
    val argTypes = 0.until(2 * setsAsCells.size) map
      { i => if (i % 2 == 0) setElemTypes(i / 2) else setsAsCells(i / 2).cellType }
    val targetSetT = rewriter.typeFinder.compute(state.ex, targetMapT +: argTypes :_*)

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
