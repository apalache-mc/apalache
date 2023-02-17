package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt._
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.ConstT1
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

class UninterpretedConstOracle(valueCells: Seq[ArenaCell], oracleCell: ArenaCell, nvalues: Int) extends Oracle {

  override def size: Int = nvalues

  override def whenEqualTo(state: SymbState, position: Int): TBuilderInstruction =
    tla.eql(oracleCell.toBuilder, valueCells(position).toBuilder)

  override def caseAssertions(
      state: SymbState,
      assertions: Seq[TBuilderInstruction],
      elseAssertions: Seq[TBuilderInstruction] = Seq.empty): TBuilderInstruction = {
    if (elseAssertions.nonEmpty && assertions.size != elseAssertions.size) {
      throw new IllegalStateException(s"Invalid call to Oracle, malformed elseAssertions")
    }

    super.caseAssertions(state, assertions, elseAssertions)
  }

  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = {
    logger.info("UIC")
    def isEqual(valueCell: ArenaCell): Boolean = {
      val eq = tla.eql(valueCell.toBuilder, oracleCell.toBuilder)
      solverContext.evalGroundExpr(eq) == tla.bool(true).build
    }

    valueCells.indexWhere(isEqual) // the oracle must be equal to one of the cached values
  }
}

object UninterpretedConstOracle {

  /**
   * Designated type to be used in this oracle.
   */
  val UNINTERPRETED_TYPE = "_ORA"

  def create(rewriter: SymbStateRewriter, state: SymbState, nvalues: Int): (SymbState, UninterpretedConstOracle) = {
    val solverAssert = rewriter.solverContext.assertGroundExpr _

    val (newArena, valueCells) =
      rewriter.modelValueCache.createAndCacheMany(state.arena, UNINTERPRETED_TYPE, 0.until(nvalues).map(_.toString))
    val nextState = state.setArena(newArena.appendCell(ConstT1(UNINTERPRETED_TYPE)))
    val oracleCell = nextState.arena.topCell
    val oracle = new UninterpretedConstOracle(valueCells, oracleCell, nvalues)
    // the oracle value must be equal to one of the value cells
    solverAssert(tla.or(0.until(nvalues).map(i => oracle.whenEqualTo(nextState, i)): _*))
    (nextState, oracle)
  }
}
