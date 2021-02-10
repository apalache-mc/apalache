package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.SymbState
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.TlaEx
import at.forsyte.apalache.tla.lir.convenience.tla

/**
 * An oracle that always has the same value. This class specializes all methods to the case oracle == fixedValue.
 * However, evalPosition always returns fixedValue.
 *
 * @param fixedValue a fixed value of the oracle
 */
class MockOracle(fixedValue: Int) extends Oracle {

  /**
   * Produce an expression that states that the oracle values equals to the given integer position.
   * The actual implementation may be different from an integer comparison.
   *
   * @param state    a symbolic state
   * @param position a position the oracle should be equal to
   */
  override def whenEqualTo(state: SymbState, position: Int): TlaEx = { tla.bool(position == fixedValue) }

  /**
   * Produce a ground expression that contains assertions for the possible oracle values.
   *
   * @param state      a symbolic state
   * @param assertions a sequence of assertions, one per oracle value
   * @return an expression ite(oracle = 0, ite(oracle = 1, ...))
   */
  override def caseAssertions(state: SymbState, assertions: Seq[TlaEx]): TlaEx = { assertions(fixedValue) }

  /**
   * Get a symbolic state and decode the value of the oracle variable into an integer.
   * This method assumes that the solver context has produced an SMT model.
   *
   * @param solverContext a solver context
   * @param state         a symbolic state
   * @return an integer value of the oracle
   */
  override def evalPosition(solverContext: SolverContext, state: SymbState): Int = { fixedValue }
}
