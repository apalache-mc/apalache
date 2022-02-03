package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.{SymbStateRewriterImpl, arraysEncoding}
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithIncrementalAndArrays
    extends TestTransitionExecutorImpl[IncrementalExecutionContextSnapshot]
    with TestFilteredTransitionExecutor[IncrementalExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver =
      new Z3SolverContext(SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = arraysEncoding))
    val rewriter = new SymbStateRewriterImpl(solver, new ExprGradeStoreImpl())
    val exeCtx = new IncrementalExecutionContext(rewriter)
    try {
      test(exeCtx)
    } finally {
      rewriter.dispose()
    }
  }
}
