package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, DefaultValueFactory, ProtoSeqOps}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir.{OperEx, TlaEx, ValEx}
import at.forsyte.apalache.tla.pp.TlaInputError

/**
 * Implements f[x] for: functions, records, and tuples.
 *
 * @author
 *   Igor Konnov
 */
class FunAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  private val picker = new CherryPick(rewriter)
  private val defaultValueFactory = new DefaultValueFactory(rewriter)
  private val proto = new ProtoSeqOps(rewriter)

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.app, _*) => true
      case _                          => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case ex @ OperEx(TlaFunOper.app, funEx, argEx) =>
        // SE-FUN-APP1
        val funState = rewriter.rewriteUntilDone(state.setRex(funEx))
        val funCell = funState.asCell

        // we use funCell.cellType, not funEx.typeTag, because funEx can be the result of the rewriter
        funCell.cellType match {
          case TupleT(_) =>
            // cheap access as `argEx` should be a literal
            applyTuple(funState, funCell, funEx, argEx)

          case RecordT(_) =>
            // cheap access as `argEx` should be a literal
            val resultT = CellT.fromTypeTag(ex.typeTag)
            applyRecord(funState, funCell, funEx, argEx, resultT)

          case SeqT(elemT) =>
            // cheap or expensive, depending on `argEx`
            applySequence(funState, funCell, argEx, elemT)

          case _ =>
            // general functions, which introduce `O(capacity)` SMT constraints.
            applyFun(funState, funCell, argEx)
        }

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName), state.ex)
    }
  }

  private def applySequence(state: SymbState, seqCell: ArenaCell, argEx: TlaEx, elemT: CellT): SymbState = {
    val (protoSeq, _, capacity) = proto.unpackSeq(state.arena, seqCell)
    val nextState = defaultValueFactory.makeUpValue(state, elemT)
    val defaultValue = nextState.asCell
    argEx match {
      case ValEx(TlaInt(indexBase1)) =>
        if (indexBase1 < 1 || indexBase1 > capacity) {
          // this is the rare case when the spec author has made a typo, e.g., f[0]
          val msg =
            s"Out of bounds error when accessing a sequence of length up to $capacity with index $indexBase1"
          throw new TlaInputError(msg, Some(state.ex.ID))
        } else {
          // accessing via the integer literal is cheap
          val elem = proto.at(nextState.arena, protoSeq, indexBase1.toInt)
          nextState.setRex(elem.toNameEx)
        }

      case _ =>
        // the general case, which introduces `O(capacity)` SMT constraints.
        proto.get(picker, defaultValue, nextState, protoSeq, argEx)
    }
  }

  private def applyRecord(state: SymbState, recordCell: ArenaCell, recEx: TlaEx, argEx: TlaEx,
      resultT: CellT): SymbState = {
    val key = argEx match {
      case ValEx(TlaStr(k)) => k
      case _ => throw new RewriterException(s"Accessing a record $recEx with a non-constant key $argEx", argEx)
    }
    val fields = recordCell.cellType match {
      case RecordT(f) => f
      case t @ _      => throw new RewriterException(s"Corrupted record $recEx of a non-record type $t", recEx)
    }
    val index = fields.keySet.toList.indexOf(key)
    val elems = state.arena.getHas(recordCell)
    if (index >= 0 && index < elems.length) {
      state.setRex(elems(index).toNameEx)
    } else {
      // The key does not belong to the record. This can happen as records of different domains can be unified
      defaultValueFactory.makeUpValue(state, resultT)
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
    state.setRex(tupleElem.toNameEx)
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
        tla.impl(tla.not(oracle.whenEqualTo(nextState, nelems)), tla.eql(pickedArg.toNameEx, argCell.toNameEx))
      // if oracle < N, then pickedArg = argCell
      solverAssert(argEqWhenNonEmpty)
      // importantly, we require oracle = N iff there is no element equal to argCell, O(N) constraints
      for ((elem, no) <- relationElems.zipWithIndex) {
        val elemArg = nextState.arena.getHas(elem).head
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((argCell, elemArg)))
        val inRel = tla.apalacheSelectInSet(elem.toNameEx, relationCell.toNameEx)
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
