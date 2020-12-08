package at.forsyte.apalache.tla.bmcmt.rules.aux

import scala.collection.mutable.{HashMap, MultiMap, Set}
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.IntTupleIterator
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{TlaOper, TlaSetOper}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}

import scala.collection.mutable

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
    var (nextState, sets) = rewriter.rewriteSeqUntilDone(state, setEs)
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
    newState.setRex(resultSetCell.toNameEx)
  }

  private def mapCellsManyArgs(state: SymbState,
                               targetSetCell: ArenaCell,
                               mapEx: TlaEx,
                               varNames: Seq[String],
                               setsAsCells: Seq[ArenaCell],
                               cellsIter: Iterator[Seq[ArenaCell]]): (SymbState, Iterable[ArenaCell]) = {
    // we could have done it with foldLeft, but that would be even less readable
    var newState = state
    // Collect target cells and the possible membership expressions in a hash map.
    // This is probably a memory-hungry solution.
    // We will replace it with a better one in an array-based SMT encoding:
    // https://github.com/informalsystems/apalache/issues/365
    var resultsToSource = new HashMap[ArenaCell, Set[TlaEx]] with MultiMap[ArenaCell, TlaEx]
    while (cellsIter.hasNext) {
      val argCells = cellsIter.next()
      val (ns, resultCell, memEx) = mapCellsManyArgsOnce(newState, targetSetCell, mapEx, varNames, setsAsCells, argCells)
      newState = ns
      resultsToSource.addBinding(resultCell, memEx)
    }

    // add the membership constraints: one per target cell
    for ((targetCell, memExpressions) <- resultsToSource) {
      val inNewSet = OperEx(TlaSetOper.in, targetCell.toNameEx, targetSetCell.toNameEx)
      val inSourceSet = {
        if (memExpressions.size == 1) {
          memExpressions.head
        } else {
          tla.or(memExpressions.toSeq: _*)
        }
      }
      // the target cell belongs to the resulting set if and only if one of its preimages belongs to the original sets
      rewriter.solverContext.assertGroundExpr(tla.eql(inNewSet, inSourceSet))
    }

    (newState, resultsToSource.keys)
  }

  private def mapCellsManyArgsOnce(state: SymbState,
                                   targetSetCell: ArenaCell,
                                   mapEx: TlaEx,
                                   varNames: Seq[String],
                                   setsAsCells: Seq[ArenaCell],
                                   valuesAsCells: Seq[ArenaCell]): (SymbState, ArenaCell, TlaEx) = {
    // bind the variables to the corresponding cells
    val newBinding: Binding = varNames.zip(valuesAsCells).foldLeft(state.binding)((m, p) => Binding(m.toMap + p))
    val mapState = state.setBinding(newBinding).setRex(mapEx)
    var nextState = rewriter.rewriteUntilDone(mapState)
    val mapResultCell = nextState.asCell

    // bug 365: what can happen here is that several tuples are mapped to exactly the same cell, e.g., a record field.
    // We have to collect all source tuples for the same cell and say that the result belongs to the set,
    // if and only if one of the source tuples belong to the source set.
    def inSourceSet(arg: ArenaCell, set: ArenaCell) = OperEx(TlaSetOper.in, arg.toNameEx, set.toNameEx)

    val argsInSourceSets = {
      if (valuesAsCells.length == 1) {
        inSourceSet(valuesAsCells.head, setsAsCells.head) // in_value_set
      } else {
        tla.and(valuesAsCells.zip(setsAsCells) map (inSourceSet _).tupled: _*) // (and in_val1_set1 ... in_valk_setk)
      }
    }
    // add the edge to the resulting set
    nextState = nextState.updateArena(_.appendHas(targetSetCell, mapResultCell))

    // reset the binding and return the resulting cell and the source membership expression
    (nextState.setBinding(state.binding), mapResultCell, argsInSourceSets)
  }
}
