package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._

/**
 * Encodes the construction of a function f = [x \in S |-> e]. We carry the domain set in a separate set cell. The
 * function's range is propagated as metadata for cex generation, but does not lead to any SMT constraints.
 *
 * @author
 *   Rodrigo Otoni
 */
class FunCtorRuleWithArrays(rewriter: SymbStateRewriter) extends FunCtorRule(rewriter) {

  override protected def rewriteFunCtor(
      state: SymbState,
      funT1: FunT1,
      mapEx: TlaEx,
      varName: String,
      setEx: TlaEx) = {
    val funT = CellT.fromType1(funT1)
    val elemT = CellT.fromType1(funT1.arg)
    val resultT = CellT.fromType1(funT1.res)

    // Rewrite the set expression into a memory cell
    var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
    val domainCell = nextState.asCell
    val domainCells = nextState.arena.getHas(domainCell)

    // We calculate and propagate the set of pairs <arg,res> for cex generation
    val pairEx = tla.tuple(tla.name(varName).typed(funT1.arg), mapEx).typed(TupT1(funT1.arg, funT1.res))
    val (afterMapPairExState, relationCells) = mapCells(nextState, pairEx, varName, setEx, domainCells)
    nextState = afterMapPairExState

    // We calculate the range of the function to generate the SMT constraints
    val (afterMapMapExState, rangeCells) = mapCells(nextState, mapEx, varName, setEx, domainCells)
    nextState = afterMapMapExState

    nextState = nextState.updateArena(_.appendCell(funT)) // An unconstrained SMT array is used to encode the function
    val funCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.setDom(funCell, domainCell))
    // We construct a set of pairs and have it store the pairs <arg,res> produced
    nextState = nextState.updateArena(_.appendCellNoSmt(FinSetT(TupleT(Seq(elemT, resultT)))))
    val relation = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendHasNoSmt(relation, relationCells: _*))
    nextState = nextState.updateArena(_.setCdm(funCell, relation))

    def addCellCons(domElem: ArenaCell, rangeElem: ArenaCell): Unit = {
      val inDomain = tla.apalacheSelectInSet(domElem.toNameEx, domainCell.toNameEx).typed(BoolT1())
      val inRange = tla.apalacheSelectInFun(domElem.toNameEx, funCell.toNameEx).typed(BoolT1())
      val eql = tla.eql(rangeElem.toNameEx, inRange).typed(BoolT1())
      val impl = tla.impl(inDomain, eql).typed(BoolT1()) // Function updates are guarded by the inDomain predicate
      rewriter.solverContext.assertGroundExpr(impl)
    }

    // Add SMT constraints
    for ((domElem, rangeElem) <- domainCells.zip(rangeCells))
      addCellCons(domElem, rangeElem)

    nextState.setRex(funCell.toNameEx)
  }
}
