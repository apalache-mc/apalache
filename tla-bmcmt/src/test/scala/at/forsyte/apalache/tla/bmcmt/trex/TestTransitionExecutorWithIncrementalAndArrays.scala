package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriterImpl
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

// TODO: Extend TestTransitionExecutorImpl and TestFilteredTransitionExecutor when development in the
//  "arrays" encoding progresses

//@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithIncrementalAndArrays {
  /*
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = new Z3SolverContext(SolverConfig(debug = false, profile = false, randomSeed = 0))
    val rewriter =
    val exeCtx = new IncrementalExecutionContext(rewriter)
    try {
      test(exeCtx)
    } finally {
      rewriter.dispose()
    }
  }
   */
}
