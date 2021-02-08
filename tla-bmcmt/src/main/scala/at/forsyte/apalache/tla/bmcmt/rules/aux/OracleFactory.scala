package at.forsyte.apalache.tla.bmcmt.rules.aux
import at.forsyte.apalache.tla.bmcmt.{SymbState, SymbStateRewriter}

class OracleFactory(rewriter: SymbStateRewriter) {

  /**
   * Create a new oracle that can have a value in the range [0, nvalues).
   * This oracle is created using the most efficient oracle implementation.
   *
   * @param state   a symbolic state
   * @param nvalues the number of values to hold
   * @return a new symbolic state and the oracle, the state.rex equals to state.rex
   */
  def newDefaultOracle(state: SymbState, nvalues: Int): (SymbState, Oracle) = {
    UninterpretedConstOracle.create(rewriter, state, nvalues)
  }

  /**
   * Create a new oracle that can have a value in the range [0, nvalues).
   * This oracle is using uninterpreted constants to encode the oracle values.
   *
   * @param state   a symbolic state
   * @param nvalues the number of values to hold
   * @return a new symbolic state and the oracle, the state.rex equals to state.rex
   */
  def newConstOracle(state: SymbState, nvalues: Int): (SymbState, UninterpretedConstOracle) = {
    UninterpretedConstOracle.create(rewriter, state, nvalues)
  }

  /**
   * Create a new oracle that can have a value in the range [0, nvalues).
   * This oracle is using a propositional encoding of oracle values,
   * e.g., 4 values are encoded as b0 /\ b1, ~b0 /\ b1, b0 /\ ~b1, ~b0 /\ ~b1.
   *
   * @param state   a symbolic state
   * @param nvalues the number of values to hold
   * @return a new symbolic state and the oracle, the state.rex equals to state.rex
   */
  def newPropositionalOracle(state: SymbState, nvalues: Int): (SymbState, PropositionalOracle) = {
    PropositionalOracle.create(rewriter, state, nvalues)
  }

  /**
   * Create a new oracle that can have a value in the range [0, nvalues).
   * This oracle is using an integer encoding of oracle values.
   *
   * @param state   a symbolic state
   * @param nvalues the number of values to hold
   * @return a new symbolic state and the oracle, the state.rex equals to state.rex
   */
  def newIntOracle(state: SymbState, nvalues: Int): (SymbState, IntOracle) = {
    IntOracle.create(rewriter, state, nvalues)
  }
}
