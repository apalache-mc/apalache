package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriterImpl
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

// TODO: Extend TestTransitionExecutorImpl when development in the "arrays" encoding progresses

//@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithOfflineAndArrays {
  /*
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext.createZ3(None, SolverConfig(debug = false, profile = false, randomSeed = 0))
    val rewriter =
    val exeCtx = new OfflineExecutionContext(rewriter)
    try {
      test(exeCtx)
    } finally {
      rewriter.dispose()
    }
  }
   */
}
