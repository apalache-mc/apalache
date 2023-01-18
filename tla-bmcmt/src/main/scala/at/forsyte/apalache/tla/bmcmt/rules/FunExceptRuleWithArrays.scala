package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.arena.SmtConstElemPtr
import at.forsyte.apalache.tla.bmcmt.rules.aux.AuxOps.constrainRelationArgs
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

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
      indexCell: ArenaCell,
      valueCell: ArenaCell): SymbState = {

    // We create an unconstrained SMT array that can be equated to funCell and updated
    var nextState = state.updateArena(_.appendCellOld(funCell.cellType, isUnconstrained = true))
    val resultFunCell = nextState.arena.topCell

    // Propagate the function's domain
    val domainCell = nextState.arena.getDom(funCell)
    nextState = nextState.updateArena(_.setDom(resultFunCell, domainCell))

    // Make pair <arg,res> to propagate metadata
    def mkPair(indexCell: ArenaCell, resCell: ArenaCell): TBuilderInstruction =
      tla.tuple(indexCell.toBuilder, resCell.toBuilder)

    nextState = rewriter.rewriteUntilDone(nextState.setRex(mkPair(indexCell, valueCell)))
    val newPairCell = nextState.asCell

    // Declare the updated set of pairs <arg,res>
    val relation = nextState.arena.getCdm(funCell)
    val relationCells = nextState.arena.getHas(relation)
    nextState = nextState.updateArena(_.appendCellNoSmt(relation.cellType))
    val resultRelation = nextState.arena.topCell

    def eachRelationPair(pair: ArenaCell): Unit = {
      val pairIndex = nextState.arena.getHas(pair).head
      val ite = tla
        .ite(tla.eql(pairIndex.toBuilder, indexCell.toBuilder), newPairCell.toBuilder, pair.toBuilder)

      nextState = rewriter.rewriteUntilDone(nextState.setRex(ite))
      val updatedCell = nextState.asCell
      nextState = nextState.updateArena(_.appendHasNoSmt(resultRelation, SmtConstElemPtr(updatedCell)))
    }

    // Add the appropriate pairs <arg,res> to resultRelation
    relationCells.foreach(eachRelationPair)
    nextState = nextState.updateArena(_.setCdm(resultFunCell, resultRelation))
    // For the decoder to work, the pairs' arguments may need to be equated to the domain elements
    nextState = constrainRelationArgs(nextState, rewriter, domainCell, resultRelation)

    // Add a constraint equating resultFunCell to funCell, since resultFunCell is initially unconstrained
    val eql = tla.eql(resultFunCell.toBuilder, funCell.toBuilder)
    rewriter.solverContext.assertGroundExpr(eql)

    // We need to constrain resultRelationElems w.r.t relationCells and newPairCell
    val resultRelationElems = nextState.arena.getHas(resultRelation)
    nextState = rewriter.lazyEq.cacheEqConstraints(nextState, resultRelationElems.zip(relationCells))
    nextState = rewriter.lazyEq.cacheEqConstraints(nextState, resultRelationElems.map((_, newPairCell)))

    // There is no need to constrain updates, only accesses
    val updateFun = tla.storeInSet(valueCell.toBuilder, resultFunCell.toBuilder, indexCell.toBuilder)
    rewriter.solverContext.assertGroundExpr(updateFun)

    nextState.setRex(resultFunCell.toBuilder)
  }
}
