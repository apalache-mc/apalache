package at.forsyte.apalache.tla.bmcmt.rules.aux

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.{SymbState, SymbStateDecoder, SymbStateRewriter}
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * An abstract version of an oracle that is used e.g. in CherryPick.
  *
  * @author Igor Konnov
  */
trait Oracle extends Serializable {
  /**
    * Produce an expression that states that the oracle values equals to the given integer position.
    * The actual implementation may be different from an integer comparison.
    *
    * @param state a symbolic state
    * @param position a position the oracle should be equal to
    */
  def whenEqualTo(state: SymbState, position: Int): TlaEx

  /**
    * Produce a ground expression that contains assertions for the possible oracle values.
    *
    * @param state a symbolic state
    * @param assertions a sequence of assertions, one per oracle value
    * @return an expression ite(oracle = 0, ite(oracle = 1, ...))
    */
  def caseAssertions(state: SymbState, assertions: Seq[TlaEx]): TlaEx

  /**
    * Get a symbolic state and decode the value of the oracle variable into an integer.
    * This method assumes that the solver context has produced an SMT model.
    *
    * @param solverContext a solver context
    * @param state a symbolic state
    * @return an integer value of the oracle
    */
  def evalPosition(solverContext: SolverContext, state: SymbState): Int
}
