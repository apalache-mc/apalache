package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{FunT1, RecT1, TlaEx}

/**
 * Implements f[x] for: functions, records, and tuples.
 *
 * @author
 *   Rodrigo Otoni
 */
class FunAppRuleWithArrays(rewriter: SymbStateRewriter) extends FunAppRule(rewriter) {

  // TODO: override applyRecord, applyTuple, and applySeq later

  override protected def applyFun(state: SymbState, funCell: ArenaCell, argEx: TlaEx): SymbState = {
    val funT1 = funCell.cellType.toTlaType1.asInstanceOf[FunT1]
    val elemT = CellT.fromType1(funT1.res)

    var nextState = rewriter.rewriteUntilDone(state.setRex(argEx))
    val argCell = nextState.asCell

    val domainCell = nextState.arena.getDom(funCell)
    val relationCell = nextState.arena.getCdm(funCell)
    val relationElems = nextState.arena.getHas(relationCell)
    val nElems = relationElems.size

    nextState = nextState.updateArena(_.appendCellOld(elemT, isUnconstrained = true)) // The cell will be unconstrained
    val res = nextState.arena.topCell

    if (nElems > 0) {
      // We compare argCell with relationElems and if an equality is found we simply propagate elemRes
      // If argCell is not comparable at the Scala level, e.g., due to quantifier use, we need to use an oracle
      val foundElem = relationElems.find(elem => nextState.arena.getHas(elem)(0) == argCell)
      if (foundElem.isDefined) {
        val elemTuple = nextState.arena.getHas(foundElem.get)
        assert(elemTuple.size == 2) // elem should always have only edges to <arg,res>
        val elemArg = elemTuple(0)
        val elemRes = elemTuple(1)
        // If argCell is comparable at the Scala level, we generate SMT constraints based on it
        val select = tla.apalacheSelectInFun(elemArg.toNameEx, funCell.toNameEx)
        val eql = tla.eql(elemRes.toNameEx, select)
        // We need the SMT eql because funCell might be unconstrained, if it originates from a function set
        rewriter.solverContext.assertGroundExpr(eql)
        return nextState.setRex(elemRes.toNameEx)
      } else {
        // We use an oracle to pick an arg for which the function is applied
        val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(nextState, nElems + 1)
        nextState = picker.pickByOracle(oracleState, oracle, relationElems, oracleState.arena.cellTrue().toNameEx)
        val pickedElem = nextState.asCell

        assert(nextState.arena.getHas(pickedElem).size == 2)
        val pickedArg = nextState.arena.getHas(pickedElem)(0)
        val pickedRes = nextState.arena.getHas(pickedElem)(1)

        // Cache the equality between the picked argument and the supplied argument, O(1) constraints
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedArg, argCell)))
        // If oracle < N, then pickedArg = argCell
        val pickedElemInDom = tla.not(oracle.whenEqualTo(nextState, nElems))
        val argEq = tla.eql(pickedArg.toNameEx, argCell.toNameEx)
        val argEqWhenNonEmpty = tla.impl(pickedElemInDom, argEq)
        rewriter.solverContext.assertGroundExpr(argEqWhenNonEmpty)

        // We require oracle = N iff there is no element equal to argCell, O(N) constraints
        for ((elem, no) <- relationElems.zipWithIndex) {
          val elemArg = nextState.arena.getHas(elem).head
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((elemArg, argCell)))
          val inDom = tla.apalacheSelectInSet(elemArg.toNameEx, domainCell.toNameEx)
          val neqArg = tla.not(rewriter.lazyEq.safeEq(elemArg, argCell))
          val found = tla.not(oracle.whenEqualTo(nextState, nElems))
          // ~inDom \/ neqArg \/ found, or equivalently, (inDom /\ elemArg = argCell) => found
          rewriter.solverContext.assertGroundExpr(tla.or(tla.not(inDom), neqArg, found))
          // oracle = i => inDom. The equality pickedArg = argCell is enforced by argEqWhenNonEmpty
          rewriter.solverContext.assertGroundExpr(tla.or(tla.not(oracle.whenEqualTo(nextState, no)), inDom))
        }

        // We simply apply the picked arg to the SMT array encoding the function, O(1) constraints
        val select = tla.apalacheSelectInFun(argCell.toNameEx, funCell.toNameEx)
        val eql = tla.eql(res.toNameEx, select)
        rewriter.solverContext.assertGroundExpr(eql)

        // The edges, dom, and cdm are forwarded below
        nextState = nextState.updateArena(_.appendHasNoSmt(res, nextState.arena.getHas(pickedRes): _*))
        pickedRes.cellType match {
          case CellTFrom(FunT1(_, _)) | FinFunSetT(_, _) =>
            nextState = nextState.updateArena(_.setDom(res, nextState.arena.getDom(pickedRes)))
            nextState = nextState.updateArena(_.setCdm(res, nextState.arena.getCdm(pickedRes)))

          case CellTFrom(RecT1(_)) =>
            // Records do not contain cdm metadata
            nextState = nextState.updateArena(_.setDom(res, nextState.arena.getDom(pickedRes)))

          case _ =>
            // do nothing
            ()
        }
      }
    }

    nextState.setRex(res.toNameEx)
  }
}
