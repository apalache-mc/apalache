package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.types.CellT

/**
  * A snapshot when using an incremental SMT solver.
  * This snapshot is quite simple: It saves the depth of the rewriter stack as well
  * as the types of the type finder.
  *
  * @author Igor Konnov
  */
class IncrementalExecutorContextSnapshot(var rewriterLevel: Int, val varTypes: Map[String, CellT]) {
}

object IncrementalExecutorContextSnapshot {
  def apply(rewriterDepth: Int, varTypes: Map[String, CellT]): IncrementalExecutorContextSnapshot = {
    new IncrementalExecutorContextSnapshot(rewriterDepth, varTypes)
  }
}