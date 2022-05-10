package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.ProtoSeqOps
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, OperEx, RecT1, SeqT1, SetT1, TlaEx, TlaType1, TupT1, ValEx}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import scalaz.unused

/**
 * Rewriting EXCEPT for functions, tuples, and records.
 *
 * @author
 *   Igor Konnov
 */
class FunExceptRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val proto = new ProtoSeqOps(rewriter)

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
          case ft @ FunT1(_, _)  => rewriteFun(nextState, funCell, ft, indexCell, valueCell)
          case rt @ RecT1(_)     => rewriteRec(nextState, funCell, rt, indexEx, valueCell)
          case tt @ TupT1(_ @_*) => rewriteTuple(nextState, funCell, tt, indexEx, valueCell)
          case SeqT1(et)         => rewriteSeq(nextState, funCell, et, indexCell, valueCell)
          case _ =>
            throw new NotImplementedError(s"EXCEPT is not implemented for $funT. Write a feature request.")
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  def rewriteFun(
      state: SymbState,
      funCell: ArenaCell,
      funT: FunT1,
      indexCell: ArenaCell,
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
    nextState = nextState.updateArena(_.appendCellOld(relation.cellType))
    val resultRelation = nextState.arena.topCell

    // introduce a new function relation that is organized as follows:
    // [ p \in f_rel |-> IF p[1] = i THEN <<i, e>> ELSE p ]
    def eachRelationPair(pair: ArenaCell): ArenaCell = {
      val tupT = TupT1(funT.arg, funT.res)
      val types = Map("p" -> tupT, "i" -> funT.arg, "b" -> BoolT1(), "r" -> SetT1(tupT))
      // Since the expression goes to the solver, we don't care about types.
      val pairIndex = nextState.arena.getHas(pair).head // this is pair[1]
      val ite = tla
        .ite(tla.eql(pairIndex.toNameEx.as(tupT), indexCell.toNameEx.as(funT.arg)).as(BoolT1()),
            newPairCell.toNameEx.as(tupT), pair.toNameEx.as(tupT))
        .as(tupT)

      nextState = rewriter.rewriteUntilDone(nextState.setRex(ite))
      val updatedCell = nextState.asCell
      // add the new cell to the arena immediately, as we are going to use the IN predicates
      nextState = nextState.updateArena(_.appendHas(resultRelation, updatedCell))
      // The new cell belongs to the new relation iff the old cell belongs to the old relation.
      val assertion = tla
        .ite(tla.apalacheSelectInSet(pair.toNameEx ? "p", relation.toNameEx ? "r") ? "b",
            tla.apalacheStoreInSet(updatedCell.toNameEx ? "p", resultRelation.toNameEx ? "r") ? "b",
            tla.apalacheStoreNotInSet(updatedCell.toNameEx ? "p", resultRelation.toNameEx ? "r") ? "b")
        .typed(types, "b")
      solverAssert(assertion)
      updatedCell
    }

    // compute all updated cells in case we are dealing with a function over non-basic indices
    relationCells.foreach(eachRelationPair)

    // cache equality constraints between the indices and the indices in the function relation
    def cacheEqForPair(p: ArenaCell): Unit = {
      val pairIndex = nextState.arena.getHas(p).head
      nextState = cacheEq(nextState, pairIndex, indexCell)
    }

    // cache all equalities
    relationCells.foreach(cacheEqForPair)

    // introduce new function
    nextState = nextState.updateArena(_.appendCellOld(funCell.cellType))
    val newFunCell = nextState.arena.topCell
    // and attach the relation to it
    nextState
      .updateArena(_.setCdm(newFunCell, resultRelation))
      .setRex(newFunCell.toNameEx)
  }

  def rewriteRec(
      state: SymbState,
      oldRecord: ArenaCell,
      recType: RecT1,
      indexEx: TlaEx,
      newValue: ArenaCell): SymbState = {

    val keyToUpdate = indexEx match {
      case ValEx(TlaStr(key)) => key
      case ex => throw new RewriterException("Expected a string when updating a record, found: " + ex, ex)
    }

    // create a new record
    var nextState = state.updateArena(_.appendCellOld(oldRecord.cellType))
    val newRecord = nextState.arena.topCell
    val domain = nextState.arena.getDom(oldRecord)
    // copy over the domain, as it does not change
    nextState = nextState.updateArena(_.setDom(newRecord, domain))

    // add the key-value pairs of the old record but update the key that was requested to be updated
    def updateOrKeep(key: String, oldValue: ArenaCell): ArenaCell = {
      if (key == keyToUpdate) {
        newValue
      } else {
        oldValue
      }
    }

    for ((key, cell) <- recType.fieldTypes.keySet.zip(nextState.arena.getHas(oldRecord))) {
      nextState = nextState.updateArena(_.appendHasNoSmt(newRecord, updateOrKeep(key, cell)))
    }

    rewriter.rewriteUntilDone(nextState.setRex(newRecord.toNameEx))
  }

  def rewriteTuple(
      state: SymbState,
      oldTuple: ArenaCell,
      @unused tupleT: TupT1,
      indexEx: TlaEx,
      newValue: ArenaCell): SymbState = {

    val indexToUpdate = indexEx match {
      case ValEx(TlaInt(index)) => index.toInt
      case ex => throw new RewriterException("Expected a number when updating a tuple, found: " + ex, ex)
    }

    // create a new tuple
    var nextState = state.updateArena(_.appendCellOld(oldTuple.cellType))
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

  // rewrite a sequence with EXCEPT semantics
  def rewriteSeq(
      state: SymbState,
      oldSeq: ArenaCell,
      elemT: TlaType1,
      indexCell: ArenaCell,
      newValue: ArenaCell): SymbState = {
    val (oldProtoSeq, len, capacity) = proto.unpackSeq(state.arena, oldSeq)

    // make an element for the new proto sequence
    def mkElem(state: SymbState, index: Int): (SymbState, ArenaCell) = {
      val oldValue = proto.at(state.arena, oldProtoSeq, index)
      val cond = tla.eql(indexCell.toNameEx, tla.int(index)).as(BoolT1())
      // IF indexCell = index THEN newValue ELSE oldValue
      val iteEx = tla.ite(cond, newValue.toNameEx, oldValue.toNameEx).as(elemT)
      val newState = rewriter.rewriteUntilDone(state.setRex(iteEx))
      (newState, newState.asCell)
    }

    // make a new proto sequence of the same capacity and the same length
    val nextState = proto.make(state, capacity, mkElem)
    val newProtoSeq = nextState.asCell
    proto.mkSeq(nextState, SeqT1(elemT), newProtoSeq, len)
  }
}
