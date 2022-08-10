package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps.constrainRelationArgs
import at.forsyte.apalache.tla.lir.TypedPredefs.{tlaExToBuilderExAsTyped, BuilderExAsTyped}
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, TlaEx, TupT1}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Rewriting EXCEPT for functions, tuples, and records.
 *
 * @author
 *   Rodrigo Otoni
 */
class FunExceptRuleWithArrays(rewriter: SymbStateRewriter) extends FunExceptRule(rewriter) {

  // TODO: override rewriteRec and rewriteTuple later

  override def rewriteFun(
      state: SymbState,
      funCell: ArenaCell,
      funT: FunT1,
      indexCell: ArenaCell,
      valueCell: ArenaCell): SymbState = {

    // We create an unconstrained SMT array that can be equated to funCell and updated
    var nextState = state.updateArena(_.appendCellOld(funCell.cellType, isUnconstrained = true))
    val resultFunCell = nextState.arena.topCell

    // Propagate the function's domain
    val domainCell = nextState.arena.getDom(funCell)
    nextState = nextState.updateArena(_.setDom(resultFunCell, domainCell))

    // Make pair <arg,res> to propagate metadata
    def mkPair(indexCell: ArenaCell, resCell: ArenaCell): TlaEx = {
      tla.tuple(indexCell.toNameEx, resCell.toNameEx).typed(TupT1(funT.arg, funT.res))
    }

    nextState = rewriter.rewriteUntilDone(nextState.setRex(mkPair(indexCell, valueCell)))
    val newPairCell = nextState.asCell

    // Declare the updated set of pairs <arg,res>
    val relation = nextState.arena.getCdm(funCell)
    val relationCells = nextState.arena.getHas(relation)
    nextState = nextState.updateArena(_.appendCellNoSmt(relation.cellType))
    val resultRelation = nextState.arena.topCell

    def eachRelationPair(pair: ArenaCell): Unit = {
      val tupT = TupT1(funT.arg, funT.res)
      val pairIndex = nextState.arena.getHas(pair).head
      val ite = tla
        .ite(tla.eql(pairIndex.toNameEx.as(tupT), indexCell.toNameEx.as(funT.arg)).as(BoolT1),
            newPairCell.toNameEx.as(tupT), pair.toNameEx.as(tupT))
        .as(tupT)

      nextState = rewriter.rewriteUntilDone(nextState.setRex(ite))
      val updatedCell = nextState.asCell
      nextState = nextState.updateArena(_.appendHasNoSmt(resultRelation, updatedCell))
    }

    // Add the appropriate pairs <arg,res> to resultRelation
    relationCells.foreach(eachRelationPair)
    nextState = nextState.updateArena(_.setCdm(resultFunCell, resultRelation))
    // For the decoder to work, the pairs' arguments may need to be equated to the domain elements
    nextState = constrainRelationArgs(nextState, rewriter, domainCell, resultRelation)

    // Add a constraint equating resultFunCell to funCell, since resultFunCell is initially unconstrained
    val eql = tla.eql(resultFunCell.toNameEx, funCell.toNameEx)
    rewriter.solverContext.assertGroundExpr(eql)

    // We need to constrain resultRelationElems w.r.t relationCells and newPairCell
    val resultRelationElems = nextState.arena.getHas(resultRelation)
    nextState = rewriter.lazyEq.cacheEqConstraints(nextState, resultRelationElems.zip(relationCells))
    nextState = rewriter.lazyEq.cacheEqConstraints(nextState, resultRelationElems.map((_, newPairCell)))

    // There is no need to constrain updates, only accesses
    val updateFun = tla.apalacheStoreInFun(valueCell.toNameEx, resultFunCell.toNameEx, indexCell.toNameEx)
    rewriter.solverContext.assertGroundExpr(updateFun)

    nextState.setRex(resultFunCell.toNameEx)
  }
}
