package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.analyses.ExprGradeStoreImpl
import at.forsyte.apalache.tla.bmcmt.smt.{RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSeqModelCheckerWithOOPSLA19 extends TestSeqModelCheckerTrait {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext
      .createZ3(None,
          SolverConfig(debug = false, profile = false, 0, z3StatsSec = 0, smtEncoding = SMTEncoding.OOPSLA19))
    val rewriter = new SymbStateRewriterImpl(solver, new IncrementalRenaming(new IdleTracker), new ExprGradeStoreImpl)
    test(rewriter)
  }
}
