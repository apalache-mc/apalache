package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.smt.SolverContext

class SymbStateRewriterAutoWithArrays(_solverContext: SolverContext) extends SymbStateRewriterAuto(_solverContext) {
  override protected val impl = new SymbStateRewriterImplWithArrays(solverContext, exprGradeStore)
}
