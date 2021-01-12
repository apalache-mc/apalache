package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriterImpl
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingZ3SolverContext, SolverConfig}
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

/**
  * The tests for TransitionExecutorImpl that are using IncrementalSnapshot.
  *
  * @author Igor Konnov
  */
@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorImplWithOffline extends AbstractTestTransitionExecutorImpl[OfflineExecutorContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val typeFinder = new TrivialTypeFinder()
    val solver = RecordingZ3SolverContext(None, SolverConfig(debug = false, profile = false, randomSeed = 0))
    val rewriter = new SymbStateRewriterImpl(solver, typeFinder, new ExprGradeStoreImpl())
    val exeCtx = new OfflineExecutorContext(rewriter)
    try {
      test(exeCtx)
    } finally {
      rewriter.dispose()
    }
  }
}
