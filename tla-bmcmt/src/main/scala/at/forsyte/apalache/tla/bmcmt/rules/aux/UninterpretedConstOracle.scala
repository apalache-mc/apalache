package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.caches.StrValueCache
import at.forsyte.apalache.tla.bmcmt.types.ConstT
import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.{TlaEx, ValEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.TlaInt

class UninterpretedConstOracle(valueCells: Seq[ArenaCell], oracleCell: ArenaCell, nvalues: Int) extends Oracle {
  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state    a symbolic state
    * @param position a position the oracle should be equal to
    */
  override def whenEqualTo(state: SymbState, position: Int): TlaEx = {
    tla.eql(oracleCell.toNameEx, valueCells(position).toNameEx)
  }

  /**
    * Produce a ground expression that contains assertions for the possible oracle values.
    *
    * @param state      a symbolic state
    * @param assertions a sequence of assertions, one per oracle value, this sequence is always truncated to nvalues
    * @return an expression ite(oracle = 0, ite(oracle = 1, ...))
    */
  override def caseAssertions(state: SymbState, assertions: Seq[TlaEx]): TlaEx = {
    nvalues match {
      case 0 => state.arena.cellTrue().toNameEx

      case 1 => assertions.head

      case _ =>
        val es = assertions.slice(0, nvalues).zipWithIndex.map
          { case (e, i) => tla.or(tla.not(whenEqualTo(state, i)), e) }
        tla.and(es :_*)
    }
  }

  /**
    * Get a symbolic state and decode the value of the oracle variable into an integer.
    * This method assumes that the solver context has produced an SMT model.
    *
    * @param solverContext a solver context
    * @param state a symbolic state
    * @return an integer value of the oracle, or -1, when the SMT encoding is broken
    */
  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    def isEqual(valueCell: ArenaCell): Boolean = {
      solverContext.evalGroundExpr(tla.eql(valueCell.toNameEx, oracleCell.toNameEx)) == tla.bool(true)
    }

    valueCells indexWhere isEqual // the oracle must be equal to one of the cached values
  }
}

object UninterpretedConstOracle {
  def create(rewriter: SymbStateRewriter, state: SymbState, nvalues: Int): (SymbState, UninterpretedConstOracle) = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _
    var nextState = state

    def introConst(i: Int): ArenaCell = {
      val (newArena, valueCell) = rewriter.strValueCache.getOrCreate(nextState.arena, i.toString)
      nextState = nextState.setArena(newArena)
      valueCell
    }

    val nums = 0 until nvalues
    val valueCells = nums map introConst // introduce a constant for every integer
    nextState = state.setArena(nextState.arena.appendCell(ConstT()))
    val oracleCell = nextState.arena.topCell
    val oracle = new UninterpretedConstOracle(valueCells, oracleCell, nvalues)
    // the oracle value must be equal to one of the value cells
    solverAssert(tla.or(nums.map(i => oracle.whenEqualTo(nextState, i)) :_*))
    (nextState, oracle)
  }
}