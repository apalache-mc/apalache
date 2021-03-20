package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.types.{CellT, FunT, RecordT, TupleT}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.UntypedPredefs
import at.forsyte.apalache.tla.lir.TlaType1
import at.forsyte.apalache.tla.lir.{FunT1, RecT1, TupT1}

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
      case _                             => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaFunOper.except, funEx, OperEx(TlaFunOper.tuple, indexEx), valueEx) =>
        // Desugarer takes care of general EXCEPT and provides us with the simple form
        // rewrite the arguments
        var nextState = state
        nextState = rewriter.rewriteUntilDone(nextState.setRex(funEx))
        val funCell = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(indexEx))
        val indexCell = nextState.asCell
        nextState = rewriter.rewriteUntilDone(nextState.setRex(valueEx))
        val valueCell = nextState.asCell
        val funT = TlaType1.fromTypeTag(ex.typeTag)
        // delegate to the code that knows how to deal with the specific type
        funT match {
          case ft @ FunT1(_, _) => rewriteFun(nextState, funCell, ft, indexCell, valueCell)
          case rt @ RecT1(_)    => rewriteRec(nextState, funCell, rt, indexEx, valueCell)
          case tt @ TupT1(_)    => rewriteTuple(nextState, funCell, tt, indexEx, valueCell)
          case _ =>
            throw new NotImplementedError(s"EXCEPT is not implemented for $funT. Write a feature request.")
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  def rewriteFun(state: SymbState, funCell: ArenaCell, funT: FunT1, indexCell: ArenaCell,
      valueCell: ArenaCell): SymbState = {
    // rewrite tuples <<j_i, e_i>> to cells
    def mkPair(indexCell: ArenaCell, resCell: ArenaCell): TlaEx = {
      tla
        .tuple(indexCell.toNameEx, resCell.toNameEx)
        .typed(TupT1(funT.arg, funT.res))
    }

    var nextState = rewriter.rewriteUntilDone(state.setRex(mkPair(indexCell, valueCell)))
    val newPairCell = nextState.asCell

    // get the function relation from the arena
    val relation = nextState.arena.getCdm(funCell)
    val relationCells = nextState.arena.getHas(relation)
    nextState = nextState.updateArena(_.appendCell(relation.cellType))
    val resultRelation = nextState.arena.topCell

    // introduce a new function relation that is organized as follows:
    // [ p \in f_rel |-> IF p[1] = i THEN <<i, e>> ELSE p ]
    def eachRelationPair(pair: ArenaCell): ArenaCell = {
      // Since the expression goes to the solver, we don't care about types.
      import UntypedPredefs._

      val ite = tla.ite(tla.eql(pair.toNameEx, indexCell.toNameEx), newPairCell.toNameEx, pair.toNameEx)

      nextState = rewriter.rewriteUntilDone(nextState.setRex(ite))
      val updatedCell = nextState.asCell
      // add the new cell to the arena immediately, as we are going to use the IN predicates
      nextState = nextState.updateArena(_.appendHas(resultRelation, updatedCell))
      // The new cell belongs to the new relation iff the old cell belongs to the old relation.
      solverAssert(tla.equiv(tla.in(pair.toNameEx, relation.toNameEx),
              tla.in(updatedCell.toNameEx, resultRelation.toNameEx)))
      updatedCell
    }

    // compute all updated cells in case we are dealing with a function over non-basic indices
    val updatedCells = relationCells map eachRelationPair

    // cache equality constraints between the indices and the indices in the function relation
    def cacheEqForPair(p: ArenaCell): Unit = {
      val pairIndex = nextState.arena.getHas(p).head
      nextState = cacheEq(nextState, pairIndex, indexCell)
    }

    // cache all equalities
    relationCells foreach cacheEqForPair

    // introduce new function
    nextState = nextState.updateArena(_.appendCell(funCell.cellType))
    val newFunCell = nextState.arena.topCell
    // and attach the relation to it
    nextState
      .updateArena(_.setCdm(newFunCell, resultRelation))
      .setRex(newFunCell.toNameEx)
  }

  def rewriteRec(state: SymbState, oldRecord: ArenaCell, recType: RecT1, indexEx: TlaEx,
      newValue: ArenaCell): SymbState = {

    val keyToUpdate = indexEx match {
      case ValEx(TlaStr(key)) => key
      case ex                 => throw new RewriterException("Expected a string when updating a record, found: " + ex, ex)
    }

    // create a new record
    var nextState = state.updateArena(_.appendCell(oldRecord.cellType))
    val newRecord = nextState.arena.topCell

    // add the key-value pairs of the old record but update the key that was requested to be updated
    def updateOrKeep(key: String, oldValue: ArenaCell): ArenaCell = {
      if (key == keyToUpdate) {
        newValue
      } else {
        oldValue
      }
    }

    for ((key, cell) <- recType.fieldTypes.keys.zip(nextState.arena.getHas(oldRecord))) {
      nextState = nextState.updateArena(_.appendHasNoSmt(newRecord, updateOrKeep(key, cell)))
    }

    rewriter.rewriteUntilDone(nextState.setRex(newRecord.toNameEx))
  }

  def rewriteTuple(state: SymbState, oldTuple: ArenaCell, tupleT: TupT1, indexEx: TlaEx,
      newValue: ArenaCell): SymbState = {

    val indexToUpdate = indexEx match {
      case ValEx(TlaInt(index)) => index.toInt
      case ex                   => throw new RewriterException("Expected a number when updating a tuple, found: " + ex, ex)
    }

    // create a new tuple
    var nextState = state.updateArena(_.appendCell(oldTuple.cellType))
    val newTuple = nextState.arena.topCell

    // add the indices of old tuple but update the index that was requested to be updated
    def updateOrKeep(index: Int, oldValue: ArenaCell): ArenaCell = {
      if (index == indexToUpdate) {
        newValue
      } else {
        oldValue
      }
    }

    for ((cell, index0based) <- nextState.arena.getHas(oldTuple).zipWithIndex) {
      nextState = nextState.updateArena(_.appendHasNoSmt(newTuple, updateOrKeep(index0based + 1, cell)))
    }

    rewriter.rewriteUntilDone(nextState.setRex(newTuple.toNameEx))
  }
}
