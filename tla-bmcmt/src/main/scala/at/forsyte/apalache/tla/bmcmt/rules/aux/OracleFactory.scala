package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.bmcmt.{ArenaCell, SymbState, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.convenience.tla

class OracleFactory(rewriter: SymbStateRewriter) {
  /**
    * Create a new oracle that can have a value in the range [0, nvalues).
    * This oracle is using uninterpreted constants to encode the oracle values.
    *
    * @param state   a symbolic state
    * @param nvalues the number of values to hold
    * @return a new symbolic state and the oracle, the state.rex equals to state.rex
    */
  def newConstOracle(state: SymbState, nvalues: Int): (SymbState, Oracle) = {
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
