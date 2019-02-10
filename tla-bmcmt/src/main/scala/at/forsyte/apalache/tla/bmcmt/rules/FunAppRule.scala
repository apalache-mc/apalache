package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.implicitConversions._
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
  private val defaultValueFactory = new DefaultValueFactory(rewriter)
  private val simplifier = new ConstSimplifier()

  override def isApplicable(symbState: SymbState): Boolean = {
    symbState.ex match {
      case OperEx(TlaFunOper.app, _*) => true
      case _ => false
    }
  }

  override def apply(state: SymbState): SymbState = {
    state.ex match {
      case OperEx(TlaFunOper.app, funEx, argEx) =>
        // SE-FUN-APP1
        val funState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(funEx))
        val funCell = funState.arena.findCellByNameEx(funState.ex)

        val finalState =
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
        rewriter.coerce(finalState, state.theory)

      case _ =>
        throw new RewriterException("%s is not applicable".format(getClass.getSimpleName))
    }
  }

  private def applyRecord(state: SymbState, recordCell: ArenaCell, recEx: TlaEx, argEx: TlaEx): SymbState = {
    val key = argEx match {
      case ValEx(TlaStr(k)) => k
      case _ => throw new RewriterException(s"Accessing a record $recEx with a non-constant key $argEx")
    }
    val fields = recordCell.cellType match {
      case RecordT(f) => f
      case t @ _ => throw new RewriterException(s"Corrupted record $recEx of a non-record type $t")
    }
    val index = fields.keySet.toList.indexOf(key)
    val elems = state.arena.getHas(recordCell)
    if (index >= 0 && index < elems.length) {
      val keyCell = rewriter.strValueCache.get(key).get
      state.setTheory(CellTheory()).setRex(elems(index))
    } else {
      // This case should have been caught by type inference. Throw an exception immediately.
      val msg = s"Accessing record $recEx of type ${recordCell.cellType} with the field $argEx. Type inference should have caught this."
      throw new IllegalArgumentException(msg)
    }
  }

  private def applyTuple(state: SymbState, tupleCell: ArenaCell, funEx: TlaEx, argEx: TlaEx): SymbState = {
    val simpleArg = simplifier.simplify(argEx)
    val index = simpleArg match {
      case ValEx(TlaInt(i)) => i.toInt - 1

      case _ =>
        throw new RewriterException("Accessing a tuple with a non-constant index: " + argEx)
    }

    val elems = state.arena.getHas(tupleCell)
    if (index < 0 || index >= elems.length) {
      throw new RewriterException(s"Out of bounds index ${index + 1} in $funEx[$argEx]")
    }

    val tupleElem = elems(index)
    state.setTheory(CellTheory()).setRex(tupleElem)
  }

  private def applySeq(state: SymbState, seqCell: ArenaCell, argEx: TlaEx): SymbState = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(argEx))
    val argCell = nextState.asCell
    val seqChildren = state.arena.getHas(seqCell)
    val start = seqChildren.head // starts with 0
    val end = seqChildren.tail.head // starts with 0
    // Get the sequence of N elements. The range values[start : end] forms the actual sequence
    val values = seqChildren.tail.tail

    // create the oracle
    val nelems = values.size
    nextState = nextState.appendArenaCell(IntT())
    val oracle = nextState.arena.topCell.toNameEx
    solverAssert(tla.ge(oracle, tla.int(0)))
    solverAssert(tla.le(oracle, tla.int(nelems)))
    // pick an element to be the result
    nextState = picker.pickByOracle(nextState, oracle, values)
    val pickedResult = nextState.asCell
    // now it is getting interesting:
    // If 1 <= arg <= end - start, just require oracle = arg - 1 + start,
    // Otherwise, set oracle to N
    val inRange = tla.and(tla.le(tla.int(1), argCell),
                          tla.le(argCell, tla.minus(end, start)))
    val oracleEqArg = tla.eql(oracle, tla.plus(tla.minus(argCell, tla.int(1)), start))
    val oracleIsN = tla.eql(oracle, tla.int(nelems))
    solverAssert(tla.or(tla.and(inRange, oracleEqArg), tla.and(tla.not(inRange), oracleIsN)))

    nextState.setRex(pickedResult).setTheory(CellTheory())
  }

  private def applyFun(state: SymbState, funCell: ArenaCell, argEx: TlaEx): SymbState = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    // SE-FUN-APP2
    var nextState = rewriter.rewriteUntilDone(state.setTheory(CellTheory()).setRex(argEx))
    val argCell = nextState.asCell

    val relationCell = nextState.arena.getCdm(funCell)
    val relationElems = nextState.arena.getHas(relationCell)
    val nelems = relationElems.size
    nextState = picker.newOracleWithDefault(nextState, relationCell, relationElems)
    val oracle = nextState.asCell

    nextState = picker.pickByOracle(nextState, oracle, relationElems)
    val pickedPair = nextState.asCell
    val pickedArg = nextState.arena.getHas(pickedPair).head
    val pickedRes = nextState.arena.getHas(pickedPair).tail.head
    // cache the equality between the picked argument and the supplied argument, O(1) constraints
    nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedArg, argCell)))
    val argEqWhenNonEmpty =
      tla.impl(tla.neql(oracle, tla.int(nelems)), tla.eql(pickedArg, argCell))
    solverAssert(argEqWhenNonEmpty)
    // importantly, we require oracle = N iff there is no element equal to argCell, O(N) constraints
    for ((elem, no) <- relationElems.zipWithIndex) {
      val elemArg = nextState.arena.getHas(elem).head
      nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((argCell, elemArg)))
      val inRel = tla.in(elem, relationCell)
      val neqArg = tla.not(rewriter.lazyEq.safeEq(elemArg, argCell))
      val found = tla.neql(oracle, tla.int(nelems))
      // ~inRel \/ neqArg \/ found
      solverAssert(tla.or(tla.not(inRel), neqArg, found))
      // oracle = i => inRel
      solverAssert(tla.impl(tla.eql(oracle, tla.int(no)), inRel))
    }

    // the following step is not important, but we do it to easy debugging:
    // if oracle = N, set the picked cell to the default value
    val resultType: CellT = funCell.cellType.asInstanceOf[FunT].resultType
    nextState = defaultValueFactory.makeUpValue(nextState, resultType)
    val defaultValue = nextState.asCell
    nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedRes, defaultValue)))
    solverAssert(tla.impl(tla.eql(oracle, tla.int(nelems)), tla.eql(pickedRes, defaultValue)))


    nextState.setRex(pickedRes.toNameEx).setTheory(CellTheory())
  }
}
