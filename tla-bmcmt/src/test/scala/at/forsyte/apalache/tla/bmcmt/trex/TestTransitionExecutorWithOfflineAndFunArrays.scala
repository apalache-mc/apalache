package at.forsyte.apalache.tla.bmcmt.trex

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.SymbStateRewriterImpl
import at.forsyte.apalache.tla.bmcmt.analyses._
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import at.forsyte.apalache.tla.pp.UniqueNameGenerator
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestTransitionExecutorWithOfflineAndFunArrays
    extends TestTransitionExecutorImpl[OfflineExecutionContextSnapshot] {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext
      .createZ3(None, SolverConfig(debug = false, profile = false, randomSeed = 0, smtEncoding = SMTEncoding.FunArrays))
    new UniqueNameGenerator
    val renaming = new IncrementalRenaming(new IdleTracker)
    val rewriter = new SymbStateRewriterImpl(solver, renaming, new ExprGradeStoreImpl())
    val exeCtx = new OfflineExecutionContext(rewriter, renaming)
    try {
      test(exeCtx)
    } finally {
      exeCtx.dispose()
    }
  }
}
