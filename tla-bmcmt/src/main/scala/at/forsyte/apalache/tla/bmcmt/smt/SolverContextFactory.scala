package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.io.OutputManager
import at.forsyte.apalache.io.config.SMTSolver

/**
 * Creates concrete SMT solver contexts from solver configuration.
 */
object SolverContextFactory {

  def create(config: SolverConfig, outputManager: Option[OutputManager] = None): SolverContext = {
    config.smtSolver match {
      case SMTSolver.Z3 =>
        new Z3SolverContext(config, outputManager)

      case SMTSolver.CVC5 =>
        new Cvc5SolverContext(config, outputManager)
    }
  }
}
