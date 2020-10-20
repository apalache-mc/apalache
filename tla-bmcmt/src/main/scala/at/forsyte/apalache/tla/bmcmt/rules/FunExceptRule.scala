package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{CellT, FunT, RecordT, TupleT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}

/**
  * Rewriting EXCEPT for functions, tuples, and records.
  *
  * @author Igor Konnov
  */
class FunExceptRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private def cacheEq(s: SymbState, l: ArenaCell, r: ArenaCell) = rewriter.lazyEq.cacheOneEqConstraint(s, l, r)

  private def solverAssert = rewriter.solverContext.assertGroundExpr _

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.except, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.except, args@_*) =>
        val funEx = args.head
        val indexEs = args.tail.zipWithIndex.filter(_._2 % 2 == 0).map(_._1)
        // first, unpack singleton tuples in indices, see the comment to the method
        val unpackedIndices = unpackSingletonIndices(indexEs)
        val valEs = args.tail.zipWithIndex.filter(_._2 % 2 == 1).map(_._1)
        assert(indexEs.size == valEs.size)

        // second, rewrite all the arguments
        val (groundState: SymbState, groundArgs: Seq[TlaEx]) =
          rewriter.rewriteSeqUntilDone(state, funEx +: (unpackedIndices ++ valEs))
        val funCell = groundState.arena.findCellByNameEx(groundArgs.head)
        val indexCells = groundArgs.slice(1, 1 + unpackedIndices.size)
          .map(groundState.arena.findCellByNameEx)
        val valueCells = groundArgs
          .slice(1 + unpackedIndices.size, 1 + unpackedIndices.size + valEs.size)
          .map(groundState.arena.findCellByNameEx)
        funCell.cellType match {
          case FunT(_, _) => rewriteFun(groundState, funCell, indexCells, valueCells)
          case rt @ RecordT(_) => rewriteRec(groundState, funCell, rt, unpackedIndices, valueCells)
          case tt @ TupleT(_) => rewriteTuple(groundState, funCell, tt, unpackedIndices, valueCells)
          case _ => throw new NotImplementedError(
            s"EXCEPT is not implemented for ${funCell.cellType}. Write a feature request.")
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  def rewriteFun(state: SymbState,
                 funCell: ArenaCell,
                 indexCells: Seq[ArenaCell],
                 valueCells: Seq[ArenaCell]): SymbState = {
    // rewrite tuples <<j_i, e_i>> to cells
    val updatePairs = indexCells.zip(valueCells) // ![j_i] = e_i
    def mkPair(indexCell: ArenaCell, resCell: ArenaCell): TlaEx = tla.tuple(indexCell.toNameEx, resCell.toNameEx)

    val (stateAfterTuples, updateTuples) =
      rewriter.rewriteSeqUntilDone(state, updatePairs map (mkPair _).tupled)
    val updateTuplesAsCells = updateTuples.map(stateAfterTuples.arena.findCellByNameEx(_))

    // get the function relation from the arena
    var nextState = stateAfterTuples
    val relation = state.arena.getCdm(funCell)
    val relationCells = nextState.arena.getHas(relation)
    nextState = nextState.updateArena(_.appendCell(relation.cellType))
    val resultRelation = nextState.arena.topCell

    // introduce a new function relation that is organized as follows:
    // [ p \in f_rel |-> IF p[1] = j_1 THEN <<j_1, e_1>> ELSE ... ELSE p ]
    def eachRelationPair(p: ArenaCell): ArenaCell = {
      val ite = toIte(nextState.arena, p, indexCells, updateTuplesAsCells)
      nextState = rewriter.rewriteUntilDone(nextState.setRex(ite))
      val updatedCell = nextState.asCell
      // add the new cell to the arena immediately, as we are going to use the IN predicates
      nextState = nextState.updateArena(_.appendHas(resultRelation, updatedCell))
      // the new cell belongs to the new relation iff the old cell belongs to the old relation
      solverAssert(tla.equiv(tla.in(p, relation), tla.in(updatedCell, resultRelation)))
      updatedCell
    }

    // compute all updated cells in case we are dealing with a function over non-basic indices
    val updatedCells = relationCells map eachRelationPair

    // cache equality constraints between the indices and the indices in the function relation
    def cacheEqForPair(p: ArenaCell): Unit = {
      val pairIndex = nextState.arena.getHas(p).head
      for (updateIndex <- indexCells) {
        nextState = cacheEq(nextState, pairIndex, updateIndex)
      }
    }

    // cache all equalities
    relationCells foreach cacheEqForPair

    // introduce new function
    nextState = nextState.updateArena(_.appendCell(funCell.cellType))
    val newFunCell = nextState.arena.topCell
    // and attach the relation to it
    nextState
      .updateArena(_.setCdm(newFunCell, resultRelation))
      .setRex(newFunCell)
  }

  def rewriteRec(state: SymbState,
                 recCell: ArenaCell,
                 recType: RecordT,
                 indexEs: Seq[TlaEx],
                 valueCells: Seq[ArenaCell]): SymbState = {
    def indexToStr: TlaEx => String = {
      case ValEx(TlaStr(key)) => key
      case ex => throw new RewriterException("Expected a string when updating a record, found: " + ex, ex)
    }

    val updatedKeys = indexEs map indexToStr
    val unchangedKeys = recType.fields.keySet.diff(Set(updatedKeys :_*))
    // create a new record
    def mkUnchanged(key: String): (TlaEx, TlaEx) = {
      (tla.str(key), tla.appFun(recCell.toNameEx, tla.str(key)))
    }
    def flattenPairs(list: Seq[TlaEx], pair: (TlaEx, TlaEx)): Seq[TlaEx] = {
      pair._1 +: pair._2 +: list
    }
    // [ [k1, v1], [k2, v2], ... ]
    val updatedPairs: Seq[(TlaEx, TlaEx)] = indexEs.zip(valueCells.map(_.toNameEx))
    val unchangedPairs: Seq[(TlaEx, TlaEx)] = unchangedKeys.toList.map(mkUnchanged)
    val newRecEx = OperEx(TlaFunOper.enum,
      (updatedPairs ++ unchangedPairs).reverse.foldLeft(Seq[TlaEx]())(flattenPairs) :_*)
    rewriter.rewriteUntilDone(state.setRex(newRecEx)) // let the rewriter handle this
  }

  def rewriteTuple(state: SymbState,
                   tupleCell: ArenaCell,
                   tupleT: TupleT,
                   indexEs: Seq[TlaEx],
                   valueCells: Seq[ArenaCell]): SymbState = {
    def indexToInt: TlaEx => Int = {
      case ValEx(TlaInt(index)) => index.toInt
      case ex => throw new RewriterException("Expected a number when updating a tuple, found: " + ex, ex)
    }

    val updatedIndices = indexEs map indexToInt
    val updateMap = Map(updatedIndices.zip(valueCells) :_*)
    def updateOrKeep(i: Int): TlaEx = {
      if (updateMap.contains(i)) {
        updateMap(i)
      } else {
        tla.appFun(tupleCell, tla.int(i))
      }
    }

    val tupleSize = tupleT.args.size
    val newTuple = tla.tuple(1.to(tupleSize) map updateOrKeep :_*)
    rewriter.rewriteUntilDone(state.setRex(newTuple)) // let the rewriter handle this
  }

  def toIte(arena: Arena, pair: ArenaCell, indexCells: Seq[ArenaCell], updatePairs: Seq[ArenaCell]): TlaEx = {
    val pairIndex = arena.getHas(pair).head // the first element of the pair is the index
    updatePairs match {
      case Seq() => pair // ... ELSE p
      case newPair +: _ =>
        val updateIndex = indexCells.head // IF p[1] = i_j
        tla.ite(tla.eql(pairIndex, updateIndex), newPair, toIte(arena, pair, indexCells.tail, updatePairs.tail))
    }
  }

  def addEqualities(state: SymbState, lhs: ArenaCell, rhs: ArenaCell): SymbState = {
    rewriter.lazyEq.cacheOneEqConstraint(state, lhs, rhs)
  }


  // This is an important step. As we receive expressions from SANY, every index argument to EXCEPT
  // is always a tuple]. For instance, the expression [f EXCEPT ![1] = 2] will be represented
  // as OperEx(TlaFunOper.except, f, <<1>>, 2). Hence, we explicitly unpack singleton tuples.
  // As for non-singleton tuples, they should be preprocessed.
  private def unpackSingletonIndices(args: Seq[TlaEx]): Seq[TlaEx] = {
    def unpack(e: TlaEx) = e match {
      case OperEx(TlaFunOper.tuple, arg) =>
        arg // unpack
      case OperEx(TlaFunOper.tuple, _*) =>
        throw new InternalCheckerError("TLA importer failed to preprocess a chained EXCEPT: " + e, e)
      case _ =>
        // complain
        throw new RewriterException("Expected a tuple as a function index, found: " + e, e)
    }

    args map unpack
  }

  private def checkType(cellType: CellT): Unit = {
    cellType match {
      case FunT(_, _) => () // o.k.
      case _ => throw new NotImplementedError(s"EXCEPT is not implemented for $cellType. Write a feature request.")
    }
  }
}
