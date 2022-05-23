package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming

class SymbStateRewriterAutoWithArrays(_solverContext: SolverContext, renaming: IncrementalRenaming)
    extends SymbStateRewriterAuto(_solverContext, renaming) {
  override protected val impl =
    new SymbStateRewriterImplWithArrays(solverContext, renaming, exprGradeStore)
}
