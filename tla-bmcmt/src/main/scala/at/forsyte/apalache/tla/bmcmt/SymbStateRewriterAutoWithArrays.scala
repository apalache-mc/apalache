package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.UniqueNameGenerator

class SymbStateRewriterAutoWithArrays(
    _solverContext: SolverContext,
    nameGenerator: UniqueNameGenerator,
    renaming: IncrementalRenaming)
    extends SymbStateRewriterAuto(_solverContext, nameGenerator, renaming) {
  override protected val impl =
    new SymbStateRewriterImplWithArrays(solverContext, renaming, exprGradeStore)
}
