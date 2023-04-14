package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.{PtrUtil, _}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.bmcmt.util.IntTupleIterator
import at.forsyte.apalache.tla.lir.TypedPredefs.TypeTagAsTlaType1
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.{SetT1, TlaEx}
import at.forsyte.apalache.tla.pp.TlaInputError

import scala.collection.mutable

/**
 * The base rules for a set map {e : x ∈ S}. This class was extracted from SetMapRule, as it was used in other rules
 * that are now obsolete. Due to the general nature of this mapping, we keep it in a separate class.
 *
 * @param rewriter
 *   the symbolic rewriter
 * @author
 *   Igor Konnov
 */
class MapBase(rewriter: SymbStateRewriter) {

  /**
   * <p>Implement a mapping { e: x_1 ∈ S_1, ..., x_n ∈ S_n }.</p>
   *
   * <p>This implementation computes the cross product and maps every cell using the map expression. It is not truly
   * symbolic, we have to find a better way.</p>
   */
  def rewriteSetMapManyArgs(
      state: SymbState,
      mapEx: TlaEx,
      varNames: Seq[String],
      setEs: Seq[TlaEx]): SymbState = {
    // first, rewrite the variable domains S_1, ..., S_n
    var (nextState, sets) = rewriter.rewriteSeqUntilDone(state, setEs)

    def findSetCellAndElemType(setCell: ArenaCell): (ArenaCell, CellT) = {
      setCell.cellType match {
        case CellTFrom(SetT1(elemType)) =>
          (setCell, CellTFrom(elemType))

        case InfSetT(elemType) =>
          throw new TlaInputError(s"Found a set map over an infinite set of $elemType. Not supported.")

        case tp @ _ => throw new NotImplementedError("A set map over %s is not implemented".format(tp))
      }
    }

    val (setsAsCells, _) = (sets.map(nextState.arena.findCellByNameEx).map(findSetCellAndElemType)).unzip
    val elemsOfSets = setsAsCells.map(nextState.arena.getHasPtr)
    val setLimits = elemsOfSets.map(_.size - 1)
    // find the types of the target expression and of the target set
    val targetMapT = mapEx.typeTag.asTlaType1()
    val targetSetT = SetT1(targetMapT)

    nextState = nextState.updateArena(_.appendCell(targetSetT))
    val resultSetCell = nextState.arena.topCell

    // enumerate all possible indices and map the corresponding tuples to cells
    def byIndex(indices: Seq[Int]): Seq[ElemPtr] =
      elemsOfSets
        .zip(indices)
        .map { case (s, i) =>
          s(i)
        }

    val tupleIter = new IntTupleIterator(setLimits).map(byIndex)

    // the SMT constraints are added right in the method
    val (newState, _) =
      mapCellsManyArgs(nextState, resultSetCell, mapEx, varNames, setsAsCells, tupleIter)

    // that's it
    newState.setRex(resultSetCell.toNameEx)
  }

  private def mapCellsManyArgs(
      state: SymbState,
      targetSetCell: ArenaCell,
      mapEx: TlaEx,
      varNames: Seq[String],
      setsAsCells: Seq[ArenaCell],
      ptrIter: Iterator[Seq[ElemPtr]]): (
      SymbState,
      Iterable[ArenaCell]) = {
    // we could have done it with foldLeft, but that would be even less readable
    var newState = state

    // Collect target cells and the possible membership expressions in a MultiDict.
    // (See https://www.javadoc.io/doc/org.scala-lang.modules/scala-collection-contrib_2.13/0.1.0/scala/collection/MultiDict.html)
    //
    // This is probably a memory-hungry solution.
    // We will replace it with a better one in an array-based SMT encoding:
    // https://github.com/informalsystems/apalache/issues/365
    val resultsToSource = mutable.MultiDict.empty[ArenaCell, TlaEx]
    for (argPtrs <- ptrIter) {
      val (ns, resultCell, memEx) =
        mapCellsManyArgsOnce(newState, targetSetCell, mapEx, varNames, setsAsCells, argPtrs)
      newState = ns
      resultsToSource.addOne(resultCell -> memEx)
    }

    // add the membership constraints: one per target cell
    for ((targetCell, memExpressions) <- resultsToSource.sets) {
      val inNewSet: TlaEx = tla.apalacheStoreInSet(targetCell.toNameEx, targetSetCell.toNameEx)
      val notInNewSet: TlaEx = tla.apalacheStoreNotInSet(targetCell.toNameEx, targetSetCell.toNameEx)
      val inSourceSet = {
        if (memExpressions.size == 1) {
          memExpressions.head
        } else {
          tla.or(memExpressions.toSeq: _*).untyped()
        }
      }
      // the target cell belongs to the resulting set if and only if one of its preimages belongs to the original sets
      rewriter.solverContext.assertGroundExpr(tla.ite(inSourceSet, inNewSet, notInNewSet))
    }

    (newState, resultsToSource.keySet)
  }

  private def mapCellsManyArgsOnce(
      state: SymbState,
      targetSetCell: ArenaCell,
      mapEx: TlaEx,
      varNames: Seq[String],
      setsAsCells: Seq[ArenaCell],
      valueCellPtrs: Seq[ElemPtr]): (
      SymbState,
      ArenaCell,
      TlaEx) = {
    val valuesAsCells = valueCellPtrs.map(_.elem)
    // bind the variables to the corresponding cells
    val newBinding: Binding =
      varNames.zip(valuesAsCells).foldLeft(state.binding) { case (m, p) => Binding(m.toMap + p) }
    val mapState = state.setBinding(newBinding).setRex(mapEx)
    var nextState = rewriter.rewriteUntilDone(mapState)
    val mapResultCell = nextState.asCell

    val tuplePtrCtor = PtrUtil.tuplePtr(valueCellPtrs)

    // bug 365: what can happen here is that several tuples are mapped to exactly the same cell, e.g., a record field.
    // We have to collect all source tuples for the same cell and say that the result belongs to the set,
    // if and only if one of the source tuples belong to the source set.
    def inSourceSet(arg: ArenaCell, set: ArenaCell): TlaEx =
      tla.apalacheSelectInSet(arg.toNameEx, set.toNameEx)

    val argsInSourceSets = {
      if (valuesAsCells.length == 1) {
        inSourceSet(valuesAsCells.head, setsAsCells.head) // in_value_set
      } else {
        tla
          .and(valuesAsCells.zip(setsAsCells).map((inSourceSet _).tupled): _*)
          .untyped() // (and in_val1_set1 ... in_valk_setk)
      }
    }
    // add the edge to the resulting set
    // the map result has the same pointer-type as the tuple in the product domain.
    nextState = nextState.updateArena(_.appendHas(targetSetCell, tuplePtrCtor(mapResultCell)))

    // reset the binding and return the resulting cell and the source membership expression
    (nextState.setBinding(state.binding), mapResultCell, argsInSourceSets)
  }
}
