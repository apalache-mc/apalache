package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriterImpl
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{SolverConfig, Z3SolverContext}
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner
import org.scalatest.{Outcome, fixture}

/**
  * The tests for TransitionExecutorImpl that are using IncrementalSnapshot.
  *
  * @author Igor Konnov
  */
@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorImplWithIncremental extends AbstractTestTransitionExecutorImpl[IncrementalSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val typeFinder = new TrivialTypeFinder()
    val solver = new Z3SolverContext(SolverConfig(debug = false, profile = false, randomSeed = 0))
    val rewriter = new SymbStateRewriterImpl(solver, typeFinder, new ExprGradeStoreImpl())
    val exeCtx = new IncrementalExecutorContext(rewriter)
    try {
      test(exeCtx)
    } finally {
      rewriter.dispose()
    }
  }
}
