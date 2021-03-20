package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.rewriter.SymbStateRewriterSnapshot
import at.forsyte.apalache.tla.bmcmt.smt.{SmtLog, SolverConfig}

/**
 * A snapshot when using a non-incremental SMT solver.
 *
 * @author Igor Konnov
 */
class OfflineExecutionContextSnapshot(val solverConfig: SolverConfig, val rewriterSnapshot: SymbStateRewriterSnapshot,
    val smtLog: SmtLog) {}
