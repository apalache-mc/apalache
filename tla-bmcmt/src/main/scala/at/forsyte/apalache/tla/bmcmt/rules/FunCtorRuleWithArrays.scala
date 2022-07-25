package at.forsyte.apalache.tla.bmcmt.rules

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.bmcmt.rules.aux.FunOps._

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
    // Rewrite the set expression into a memory cell
    var nextState = rewriter.rewriteUntilDone(state.setRex(setEx))
    val domainCell = nextState.asCell
    val domainCells = nextState.arena.getHas(domainCell)

    // We calculate and propagate the set of pairs <arg,res> for cex generation
    val pairEx = tla.tuple(tla.name(varName).typed(funT1.arg), mapEx).typed(TupT1(funT1.arg, funT1.res))
    val (afterMapPairExState, relationCells) = mapCells(nextState, pairEx, varName, domainCells)
    nextState = afterMapPairExState

    // A constant SMT array constrained to a default value is used to encode the function
    // Constant arrays are used to allow for sound use of SMT equality of functions
    // TODO: consider making array constraining consistent with CherryPick.pickFunFromFunSet
    nextState = nextState.updateArena(_.appendCell(funT1))
    val funCell = nextState.arena.topCell
    nextState = nextState.updateArena(_.setDom(funCell, domainCell))
    // We construct a set of pairs and have it store the pairs <arg,res> produced
    nextState = nextState.updateArena(_.appendCellNoSmt(CellTFrom(SetT1(TupT1(funT1.arg, funT1.res)))))
    val relation = nextState.arena.topCell
    nextState = nextState.updateArena(_.appendHasNoSmt(relation, relationCells: _*))
    nextState = nextState.updateArena(_.setCdm(funCell, relation))
    // For the decoder to work, the pairs' arguments may need to be constrained
    nextState = constrainRelationArgs(nextState, rewriter, domainCell, relation)

    def addCellCons(domElem: ArenaCell, rangeElem: ArenaCell): Unit = {
      // inDomain with lazy equality
      val domElems = nextState.arena.getHas(domainCell)
      nextState = rewriter.lazyEq.cacheEqConstraints(nextState, domElems.map((_, domElem)))

      def inAndEq(elem: ArenaCell) = {
        tla
          .and(tla.apalacheSelectInSet(elem.toNameEx, domainCell.toNameEx).typed(BoolT1),
              rewriter.lazyEq.safeEq(elem, domElem))
          .typed(BoolT1) // use lazy equality
      }

      nextState = nextState.updateArena(_.appendCell(BoolT1))
      val inDomain = nextState.arena.topCell.toNameEx.typed(BoolT1)

      val elemsInAndEq = nextState.arena.getHas(domainCell).map(inAndEq)
      rewriter.solverContext.assertGroundExpr(tla.eql(inDomain, tla.or(elemsInAndEq: _*).typed(BoolT1)).typed(BoolT1))

      // val inDomain = tla.apalacheSelectInSet(domElem.toNameEx, domainCell.toNameEx).typed(BoolT1)
      val inRange = tla.apalacheStoreInFun(rangeElem.toNameEx, funCell.toNameEx, domElem.toNameEx).typed(BoolT1)
      val notInRange = tla.apalacheStoreNotInFun(rangeElem.toNameEx, funCell.toNameEx).typed(BoolT1)
      // Function updates are guarded by the inDomain predicate
      val ite = tla.ite(inDomain, inRange, notInRange).typed(BoolT1)
      rewriter.solverContext.assertGroundExpr(ite)
    }

    // Add SMT constraints
    val rangeCells = relationCells.map(c => nextState.arena.getHas(c)(1))
    for ((domElem, rangeElem) <- domainCells.zip(rangeCells))
      addCellCons(domElem, rangeElem)

    nextState.setRex(funCell.toNameEx)
  }
}
