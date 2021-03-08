package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
import at.forsyte.apalache.tla.bmcmt.rewriter.ConstSimplifierForSmt
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, DefaultValueFactory}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}

/**
 * Implements f[x] for: functions, records, and tuples.
 *
 * @author Igor Konnov
 */
class FunAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)
  private val simplifier = new ConstSimplifierForSmt()
  private val defaultValueFactory = new DefaultValueFactory(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.app, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        // SE-FUN-APP1
        val funState = rewriter.rewriteUntilDone(state.setRex(funEx))
        val funCell = funState.asCell

        funCell.cellType match {
          case TupleT(_) =>
            applyTuple(funState, funCell, funEx, argEx)

          case RecordT(_) =>
            applyRecord(funState, funCell, funEx, argEx)

          case SeqT(_) =>
            applySeq(funState, funCell, argEx)

          case _ => // general functions
            applyFun(funState, funCell, argEx)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def applyRecord(state: SymbState, recordCell: ArenaCell, recEx: TlaEx, argEx: TlaEx): SymbState = {
    val key = argEx match {
      case ValEx(TlaStr(k)) => k
      case _                => throw new RewriterException(s"Accessing a record $recEx with a non-constant key $argEx", argEx)
    }
    val fields = recordCell.cellType match {
      case RecordT(f) => f
      case t @ _      => throw new RewriterException(s"Corrupted record $recEx of a non-record type $t", recEx)
    }
    val index = fields.keySet.toList.indexOf(key)
    val elems = state.arena.getHas(recordCell)
    if (index >= 0 && index < elems.length) {
      state.setRex(elems(index))
    } else {
      // This case should have been caught by type inference. Throw an exception immediately.
      val msg =
        s"Accessing record $recEx of type ${recordCell.cellType} with the field $argEx. Type inference should have caught this."
      throw new IllegalArgumentException(msg)
    }
  }

  private def applyTuple(state: SymbState, tupleCell: ArenaCell, funEx: TlaEx, argEx: TlaEx): SymbState = {
    val index = argEx match {
      case ValEx(TlaInt(i)) => i.toInt - 1

      case _ =>
        throw new RewriterException(s"Accessing a tuple $funEx with a non-constant index $argEx", argEx)
    }

    val elems = state.arena.getHas(tupleCell)
    if (index < 0 || index >= elems.length) {
      throw new RewriterException(s"Out of bounds index ${index + 1} in $funEx[$argEx]", funEx)
    }

    val tupleElem = elems(index)
    state.setRex(tupleElem)
  }

  private def applySeq(state: SymbState, seqCell: ArenaCell, argEx: TlaEx): SymbState = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = rewriter.rewriteUntilDone(state.setRex(argEx))
    val argCell = nextState.asCell
    val seqChildren = state.arena.getHas(seqCell)
    val start = seqChildren.head // starts with 0
    val end = seqChildren.tail.head // starts with 0
    // Get the sequence of N elements. The range values[start : end] forms the actual sequence
    val values = seqChildren.tail.tail

    val nelems = values.size
    if (nelems == 0) {
      // The sequence is statically empty. Return the default value.
      // Most likely, this expression will be never used as a result.
      defaultValueFactory.makeUpValue(nextState, seqCell.cellType.asInstanceOf[SeqT].res)
    } else {
      // create the oracle
      val (oracleState, oracle) = picker.oracleFactory.newIntOracle(nextState, nelems + 1)
      nextState = oracleState
      // pick an element to be the result
      nextState = picker.pickByOracle(nextState, oracle, values, nextState.arena.cellTrue().toNameEx)
      val pickedResult = nextState.asCell
      // now it is getting interesting:
      // If 1 <= arg <= end - start, just require oracle = arg - 1 + start,
      // Otherwise, set oracle to N
      val inRange = tla.and(tla.le(tla.int(1), argCell), tla.le(argCell, tla.minus(end, start)))
      nextState = rewriter.rewriteUntilDone(nextState.setRex(tla.plus(tla.minus(argCell, tla.int(1)), start)))
      val indexCell = nextState.asCell
      val oracleEqArg = tla.eql(indexCell, oracle.intCell)
      val oracleIsN = oracle.whenEqualTo(nextState, nelems)
      solverAssert(tla.or(tla.and(inRange, oracleEqArg), tla.and(tla.not(inRange), oracleIsN)))
      nextState.setRex(pickedResult)
    }
  }

  private def applyFun(state: SymbState, funCell: ArenaCell, argEx: TlaEx): SymbState = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    // SE-FUN-APP2
    var nextState = rewriter.rewriteUntilDone(state.setRex(argEx))
    val argCell = nextState.asCell

    val relationCell = nextState.arena.getCdm(funCell)
    val relationElems = nextState.arena.getHas(relationCell)
    val nelems = relationElems.size
    if (nelems == 0) {
      // Just return a default value. Most likely, this expression will never propagate.
      defaultValueFactory.makeUpValue(nextState, funCell.cellType.asInstanceOf[FunT].resultType)
    } else {
      val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(nextState, relationElems.size + 1)
      nextState = oracleState
      nextState = picker.pickByOracle(nextState, oracle, relationElems, nextState.arena.cellTrue().toNameEx)
      val pickedPair = nextState.asCell
      val pickedArg = nextState.arena.getHas(pickedPair).head
      val pickedRes = nextState.arena.getHas(pickedPair).tail.head
      // cache the equality between the picked argument and the supplied argument, O(1) constraints
      nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedArg, argCell)))
      val argEqWhenNonEmpty =
        tla.impl(tla.not(oracle.whenEqualTo(nextState, nelems)), tla.eql(pickedArg, argCell))
      // if oracle < N, then pickedArg = argCell
      solverAssert(argEqWhenNonEmpty)
      // importantly, we require oracle = N iff there is no element equal to argCell, O(N) constraints
      for ((elem, no) <- relationElems.zipWithIndex) {
        val elemArg = nextState.arena.getHas(elem).head
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((argCell, elemArg)))
        val inRel = tla.in(elem, relationCell)
        val neqArg = tla.not(rewriter.lazyEq.safeEq(elemArg, argCell))
        val found = tla.not(oracle.whenEqualTo(nextState, nelems))
        // ~inRel \/ neqArg \/ found, or equivalently, (inRel /\ elemArg = argCell) => found
        solverAssert(tla.or(tla.not(inRel), neqArg, found))
        // oracle = i => inRel. The equality pickedArg = argCell is enforced by argEqWhenNonEmpty
        solverAssert(tla.or(tla.not(oracle.whenEqualTo(nextState, no)), inRel))
      }

      // If oracle = N, the picked cell is not constrained. In the past, we used a default value here,
      // but it sometimes produced conflicts (e.g., a picked record domain had to coincide with a default domain)
      nextState.setRex(pickedRes.toNameEx)
    }
  }
}
