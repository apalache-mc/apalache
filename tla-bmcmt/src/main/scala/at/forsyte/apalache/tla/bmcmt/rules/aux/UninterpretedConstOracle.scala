package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.caches.StrValueCache
import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

class UninterpretedConstOracle(strValueCache: StrValueCache, oracleCell: ArenaCell) extends Oracle {
  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state    a symbolic state
    * @param position a position the oracle should be equal to
    */
  override def oracleEqTo(state: SymbState, position: Int): TlaEx = {
    val strVal = strValueCache.get(position.toString)
    assert(strVal.isDefined)
    tla.eql(oracleCell.toNameEx, strVal.get.toNameEx)
  }
}

object UninterpretedConstOracle {
  def create(rewriter: SymbStateRewriter, state: SymbState, nvalues: Int): (SymbState, Oracle) = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = state.setArena(state.arena.appendCell(ConstT()))
    val oracleCell = nextState.arena.topCell
    val oracle = new UninterpretedConstOracle(rewriter.strValueCache, oracleCell)

    def introConst(i: Int): Unit = {
      val (newArena, _) = rewriter.strValueCache.getOrCreate(nextState.arena, i.toString)
      nextState = nextState.setArena(newArena)
    }

    val nums = 0 until nvalues
    nums foreach introConst // introduce a constant for every integer
    solverAssert(tla.or(nums.map(i => oracle.oracleEqTo(nextState, i)) :_*))
    (nextState, oracle)
  }
}