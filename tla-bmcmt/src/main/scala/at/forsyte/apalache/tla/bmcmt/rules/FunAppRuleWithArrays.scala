package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.types.{tlaU => tla}
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, RecT1, SetT1, TlaEx}

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
        val Seq(elemArg, elemRes) = elemTuple
        // If argCell is comparable at the Scala level, we generate SMT constraints based on it
        val select = tla.selectInFun(elemArg.toBuilder, funCell.toBuilder)
        val eql = tla.eql(elemRes.toBuilder, select)
        val impl = tla.impl(tla.selectInSet(elemArg.toBuilder, domainCell.toBuilder), eql)
        // We need the SMT eql because funCell might be unconstrained, if it originates from a function set
        // The constraining only happens if argCell is in the domain
        rewriter.solverContext.assertGroundExpr(impl)
        return nextState.setRex(elemRes.toBuilder)
      } else {
        // We use an oracle to pick an arg for which the function is applied
        val (oracleState, oracle) = picker.oracleFactory.newDefaultOracle(nextState, nElems + 1)
        nextState = picker.pickByOracle(oracleState, oracle, relationElems, oracleState.arena.cellTrue().toBuilder)
        val pickedElem = nextState.asCell

        assert(nextState.arena.getHas(pickedElem).size == 2)
        val Seq(pickedArg, pickedRes) = nextState.arena.getHas(pickedElem)

        // Cache the equality between the picked argument and the supplied argument, O(1) constraints
        nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((pickedArg, argCell)))
        // If oracle < N, then pickedArg = argCell
        val pickedElemInDom = tla.not(oracle.whenEqualTo(nextState, nElems))
        val argEq = tla.eql(pickedArg.toBuilder, argCell.toBuilder)
        val argEqWhenNonEmpty = tla.impl(pickedElemInDom, argEq)
        rewriter.solverContext.assertGroundExpr(argEqWhenNonEmpty)

        // We require oracle = N iff there is no element equal to argCell, O(N) constraints
        for ((elem, no) <- relationElems.zipWithIndex) {
          val elemArg = nextState.arena.getHas(elem).head
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, Seq((elemArg, argCell)))

          // Domain memberhsip with lazy equality
          val domElems = nextState.arena.getHas(domainCell)
          nextState = rewriter.lazyEq.cacheEqConstraints(nextState, domElems.map((_, elemArg)))

          nextState = nextState.updateArena(_.appendCell(BoolT1))
          val inDom = nextState.arena.topCell.toBuilder
          // inAndEq checks if elemArg is in domainCell
          val elemsInAndEq = domElems.map(inAndEq(rewriter, _, elemArg, domainCell, lazyEq = true))
          rewriter.solverContext.assertGroundExpr(tla.eql(inDom, tla.or(elemsInAndEq: _*)))

          val neqArg = tla.not(rewriter.lazyEq.safeEq(elemArg, argCell))
          val found = tla.not(oracle.whenEqualTo(nextState, nElems))
          // ~inDom \/ neqArg \/ found, or equivalently, (inDom /\ elemArg = argCell) => found
          rewriter.solverContext.assertGroundExpr(tla.or(tla.not(inDom), neqArg, found))
          // oracle = i => inDom. The equality pickedArg = argCell is enforced by argEqWhenNonEmpty
          rewriter.solverContext
            .assertGroundExpr(tla.or(tla.not(oracle.whenEqualTo(nextState, no)), inDom))
        }

        // We simply apply the picked arg to the SMT array encoding the function, O(1) constraints
        val select = tla.selectInFun(argCell.toBuilder, funCell.toBuilder)
        val eql = tla.eql(res.toBuilder, select)
        rewriter.solverContext.assertGroundExpr(eql)

        // The edges, dom, and cdm are forwarded below
        if (
            rewriter.solverContext.config.smtEncoding == SMTEncoding.FunArrays &&
            pickedRes.cellType.toTlaType1.isInstanceOf[SetT1]
        ) {
          // If sets are not SMT arrays, their inPreds need to be declared
          nextState = nextState.updateArena(_.appendHas(res, nextState.arena.getHasPtr(pickedRes): _*))
        } else {
          nextState = nextState.updateArena(_.appendHasNoSmt(res, nextState.arena.getHasPtr(pickedRes): _*))
        }
        pickedRes.cellType match {
          case CellTFrom(FunT1(_, _)) | FinFunSetT(_, _) =>
            nextState = nextState.updateArena(_.setDom(res, nextState.arena.getDom(pickedRes)))
            nextState = nextState.updateArena(_.setCdm(res, nextState.arena.getCdm(pickedRes)))
            // For the decoder to work, the relation's arguments may need to be equated to the domain elements
            val resDomain = nextState.arena.getDom(res)
            val resRelation = nextState.arena.getCdm(res)
            nextState = constrainRelationArgs(nextState, rewriter, resDomain, resRelation)

          case CellTFrom(RecT1(_)) =>
            // Records do not contain cdm metadata
            nextState = nextState.updateArena(_.setDom(res, nextState.arena.getDom(pickedRes)))

          case CellTFrom(SetT1(_)) =>
            if (rewriter.solverContext.config.smtEncoding == SMTEncoding.FunArrays) {
              // If funApp results in a QF_UF set, we need establish the equality between res and pickedRes, as this is
              // not inherit to the encoding with QF_UF
              nextState = rewriter.lazyEq.cacheOneEqConstraint(nextState, res, pickedRes)
              rewriter.solverContext.assertGroundExpr(tla.eql(res.toBuilder, pickedRes.toBuilder))
            }

          case _ =>
            // do nothing
            ()
        }
      }
    }

    nextState.setRex(res.toBuilder)
  }
}
