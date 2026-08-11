package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.io.OutputWorkspace
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming

class SymbStateRewriterAutoWithFunArrays(
    _solverContext: SolverContext,
    renaming: IncrementalRenaming,
    outputWorkspace: OutputWorkspace)
    extends SymbStateRewriterAuto(_solverContext, renaming, outputWorkspace) {
  override protected val impl =
    new SymbStateRewriterImplWithFunArrays(solverContext, renaming, exprGradeStore, outputWorkspace = outputWorkspace)
}
