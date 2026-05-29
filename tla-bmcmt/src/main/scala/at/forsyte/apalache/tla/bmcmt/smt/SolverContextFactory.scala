package at.forsyte.apalache.tla.bmcmt.smt

import at.forsyte.apalache.infra.passes.options.SMTSolver

/**
 * Creates concrete SMT solver contexts from solver configuration.
 */
object SolverContextFactory {

  def create(config: SolverConfig): SolverContext = {
    config.smtSolver match {
      case SMTSolver.Z3 =>
        new Z3SolverContext(config)

      case SMTSolver.CVC5 =>
        new Cvc5SolverContext(config)
    }
  }
}
