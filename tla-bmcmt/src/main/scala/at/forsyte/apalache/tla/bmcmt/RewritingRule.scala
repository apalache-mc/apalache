package at.forsyte.apalache.tla.bmcmt

/**
  * A single rewriting rule that implements operational semantics.
  */
trait RewritingRule {
  def isApplicable(symbState: SymbState): Boolean

  def apply(symbState: SymbState): SymbState

  def logOnEntry(solverContext: SolverContext, state: SymbState): SymbState = {
    solverContext.log("; %s(%s) {".format(getClass.getSimpleName, state.ex))
    state
  }

  def logOnReturn(solverContext: SolverContext, state: SymbState): SymbState = {
    solverContext.log("; } %s returns %s [%d arena cells])"
      .format(getClass.getSimpleName, state.ex, state.arena.cellCount))
    state
  }
}
