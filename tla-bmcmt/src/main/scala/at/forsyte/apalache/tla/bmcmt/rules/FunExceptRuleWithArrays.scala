package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.lir.TypedPredefs.BuilderExAsTyped
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{BoolT1, FunT1, TlaEx, TupT1}
import at.forsyte.apalache.tla.lir.UntypedPredefs._

/**
 * Rewriting EXCEPT for functions, tuples, and records.
 *
 * @author Rodrigo Otoni
 */
class FunExceptRuleWithArrays(rewriter: SymbStateRewriter) extends FunExceptRule(rewriter) {

  // TODO: override rewriteRec and rewriteTuple later

  override def rewriteFun(state: SymbState, funCell: ArenaCell, funT: FunT1, indexCell: ArenaCell,
      valueCell: ArenaCell): SymbState = {

    var nextState = state.updateArena(_.appendCell(funCell.cellType))
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
    nextState = nextState.updateArena(_.appendCellWithoutDeclaration(relation.cellType))
    val resultRelation = nextState.arena.topCell

    def eachRelationPair(pair: ArenaCell) = {
      val tupT = TupT1(funT.arg, funT.res)
      val pairIndex = nextState.arena.getHas(pair).head
      val ite = tla
        .ite(tla.eql(pairIndex.toNameEx ? "p", indexCell.toNameEx ? "i") ? "b", newPairCell.toNameEx ? "p",
            pair.toNameEx ? "p")
        .typed(Map("p" -> tupT, "i" -> funT.arg, "b" -> BoolT1()), "p")

      nextState = rewriter.rewriteUntilDone(nextState.setRex(ite))
      val updatedCell = nextState.asCell
      nextState = nextState.updateArena(_.appendHasNoSmt(resultRelation, updatedCell))
    }

    // Add the appropriate pairs <arg,res> to resultRelation
    relationCells foreach eachRelationPair
    nextState = nextState.updateArena(_.setCdm(resultFunCell, resultRelation))

    // Add a constraint equating resultFunCell to funCell
    val eql = tla.eql(resultFunCell.toNameEx, funCell.toNameEx)
    rewriter.solverContext.assertGroundExpr(eql)

    // Add a constraint updating resultFunCell if needed
    val inDomain = tla.apalacheSelectInFun(indexCell.toNameEx, domainCell.toNameEx)
    val updateFun = tla.apalacheStoreInFun(valueCell.toNameEx, resultFunCell.toNameEx, indexCell.toNameEx)
    val unchanged = tla.apalacheStoreNotInFun(valueCell.toNameEx, resultFunCell.toNameEx)
    val ite = tla.ite(inDomain, updateFun, unchanged)
    rewriter.solverContext.assertGroundExpr(ite)

    nextState.setRex(resultFunCell.toNameEx)
  }
}
