package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.SearchDirection

/**
  * A single rewriting rule that implements operational semantics.
  */
trait RewritingRule {
  def isApplicable(symbState: SymbState): Boolean

  def apply(symbState: SymbState, dir: SearchDirection): SymbState
}
