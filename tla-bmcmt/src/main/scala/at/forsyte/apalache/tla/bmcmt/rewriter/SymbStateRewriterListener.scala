package at.forsyte.apalache.tla.bmcmt.rewriter

import at.forsyte.apalache.tla.bmcmt.smt.SolverContextMetrics
import at.forsyte.apalache.tla.lir.TlaEx

/**
  * A listener that is called when an expression is rewritten.
  *
  * @author Igor Konnov
  */
trait SymbStateRewriterListener {
  def onRewrite(translatedEx: TlaEx, metricsDelta: SolverContextMetrics): Unit = {
  }

  def dispose(): Unit = {
  }
}
