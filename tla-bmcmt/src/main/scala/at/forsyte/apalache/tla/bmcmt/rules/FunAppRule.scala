package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.{CherryPick, ProtoSeqOps, RecordAndVariantOps}
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import at.forsyte.apalache.tla.lir.values.{TlaInt, TlaStr}
import at.forsyte.apalache.tla.lir._

/**
 * Implements f[x] for: functions, records, and tuples.
 *
 * @author
 *   Igor Konnov
 */
class FunAppRule(rewriter: SymbStateRewriter) extends RewritingRule {
  protected val picker = new CherryPick(rewriter)
  private val proto = new ProtoSeqOps(rewriter)
  private val recordOps = new RecordAndVariantOps(rewriter)

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
          case CellTFrom(TupT1(_ @_*)) =>
            // cheap access as `argEx` should be a literal
            applyTuple(funState, funCell, funEx, argEx)

          case CellTFrom(RecT1(_)) =>
            // cheap access as `argEx` should be a literal
            val resultT = CellT.fromTypeTag(ex.typeTag)
            applyRecord(funState, funCell, funEx, argEx, resultT)

          case CellTFrom(RecRowT1(_)) =>
            val fieldValue = recordOps.getField(funState.arena, funCell, getFieldName(argEx))
            funState.setRex(fieldValue.toNameEx)

          case CellTFrom(SeqT1(elemT)) =>
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

  private def applySequence(
      state: SymbState,
      seqCell: ArenaCell,
      argEx: TlaEx,
      elemT: TlaType1): SymbState = {
    val (protoSeq, _, capacity) = proto.unpackSeq(state.arena, seqCell)
    val (newArena, defaultValue) = rewriter.defaultValueCache.getOrCreate(state.arena, elemT)
    val nextState = state.setArena(newArena)
    argEx match {
      case ValEx(TlaInt(indexBase1)) =>
        if (indexBase1 < 1 || indexBase1 > capacity) {
          // This is the rare case when the spec author has made a typo, e.g., f[0].
          // We cannot throw an error even in this case, as it would report an error in a legal specification, e.g.,
          // 0 \in DOMAIN f \/ f[0] /= 1
          nextState.setRex(defaultValue.toNameEx)
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

  private def getFieldName(argEx: TlaEx): String = {
    argEx match {
      case ValEx(TlaStr(key)) => key
      case _ => throw new RewriterException(s"Accessing a record with value that cannot be a key $argEx", argEx)
    }
  }

  private def applyRecord(
      state: SymbState,
      recordCell: ArenaCell,
      recEx: TlaEx,
      argEx: TlaEx,
      resultT: CellT): SymbState = {
    val key = getFieldName(argEx)
    val fields = recordCell.cellType match {
      case CellTFrom(RecT1(f)) => f
      case t @ _               => throw new RewriterException(s"Corrupted record $recEx of a non-record type $t", recEx)
    }
    val index = fields.keySet.toList.indexOf(key)
    val elems = state.arena.getHas(recordCell)
    if (index >= 0 && index < elems.length) {
      state.setRex(elems(index).toNameEx)
    } else {
      // The key does not belong to the record. This can happen as records of different domains can be unified
      val (newArena, defaultValue) = rewriter.defaultValueCache.getOrCreate(state.arena, resultT.toTlaType1)
      state.setArena(newArena).setRex(defaultValue.toNameEx)
    }
  }

  private def applyTuple(
      state: SymbState,
      tupleCell: ArenaCell,
      funEx: TlaEx,
      argEx: TlaEx): SymbState = {
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

  protected def applyFun(state: SymbState, funCell: ArenaCell, argEx: TlaEx): SymbState = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    // SE-FUN-APP2
    var nextState = rewriter.rewriteUntilDone(state.setRex(argEx))
    val argCell = nextState.asCell

    val relationCell = nextState.arena.getCdm(funCell)
    val relationElems = nextState.arena.getHas(relationCell)
    val nelems = relationElems.size
    if (nelems == 0) {
      // Just return the default value. Most likely, this expression will never propagate.
      val funT = funCell.cellType.toTlaType1
      funT match {
        case FunT1(_, resultT) =>
          val (newArena, defaultValue) = rewriter.defaultValueCache.getOrCreate(nextState.arena, resultT)
          nextState.setArena(newArena).setRex(defaultValue.toNameEx)

        case _ =>
          throw new IllegalStateException(s"Expected a function, found: $funT")
      }
    } else {
      // TODO: Disabled because of #2338. Once pointers are introduced, we can potentially recover the optimization
      val foundPair = None // relationElems.find(pair => nextState.arena.getHas(pair).head == argCell)
      if (foundPair.isDefined) {
        // Feeling lucky. The cell argCell belongs to the relation. Return the result.
        val result = nextState.arena.getHas(foundPair.get)(1)
        nextState.setRex(result.toNameEx)
      } else {
        // The general case. Another cell in the relation may be equal to argCell. However, only SMT can figure that out.
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
}
