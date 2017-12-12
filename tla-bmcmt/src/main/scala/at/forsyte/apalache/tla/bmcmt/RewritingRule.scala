package at.forsyte.apalache.tla.bmcmt

/**
  * A single rewriting rule that implements operational semantics.
  */
trait RewritingRule {
  def isApplicable(symbState: SymbState): Boolean

  def apply(symbState: SymbState): SymbState

  def logOnEntry(state: SymbState): Unit = {
    state.solverCtx.log("; %s(%s) {".format(getClass.getSimpleName, state.ex))
  }

  def logOnReturn(state: SymbState): SymbState = {
    state.solverCtx.log("; } %s returns %s)".format(getClass.getSimpleName, state.ex))
    state
  }
}
