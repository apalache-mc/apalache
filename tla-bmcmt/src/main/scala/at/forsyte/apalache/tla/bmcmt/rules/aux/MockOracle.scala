package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.SymbState
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla

/**
 * An oracle that always has the same value. This class specializes all methods to the case oracle == fixedValue.
 * However, evalPosition always returns fixedValue.
 *
 * @param fixedValue
 *   a fixed value of the oracle
 */
class MockOracle(fixedValue: Int) extends Oracle {

  override def size: Int = fixedValue + 1

  override def whenEqualTo(state: SymbState, position: Int): TBuilderInstruction = {
    tla.bool(position == fixedValue)
  }

  override def caseAssertions(
      state: SymbState,
      assertions: Seq[TBuilderInstruction],
      elseAssertions: Seq[TBuilderInstruction] = Seq.empty): TBuilderInstruction =
    assertions(fixedValue)

  override def evalPosition(solverContext: SolverContext, state: SymbState): Int =
    fixedValue
}
