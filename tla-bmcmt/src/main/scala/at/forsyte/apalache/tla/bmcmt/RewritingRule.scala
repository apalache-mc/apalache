package at.forsyte.apalache.tla.bmcmt

/**
  * A single rewriting rule that implements operational semantics.
  */
trait RewritingRule {
  def isApplicable(symbState: SymbState): Boolean

  def apply(symbState: SymbState): SymbState
}
