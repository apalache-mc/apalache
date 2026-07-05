package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.{SMTEncoding, SMTSolver}
import at.forsyte.apalache.tla.bmcmt.analyses.ExprGradeStoreImpl
import at.forsyte.apalache.tla.bmcmt.smt.{Cvc5SolverContext, RecordingSolverContext, SolverConfig}
import at.forsyte.apalache.tla.lir.transformations.impl.IdleTracker
import at.forsyte.apalache.tla.lir.transformations.standard.IncrementalRenaming
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSeqModelCheckerWithCvc5OOPSLA19 extends TestSeqModelCheckerTrait {
  override protected def withFixture(test: OneArgTest): Outcome = {
    val solver = RecordingSolverContext.create(None,
        SolverConfig.default.copy(smtEncoding = SMTEncoding.OOPSLA19, smtSolver = SMTSolver.CVC5, z3StatsSec = 0))
    assert(solver.solverImpl.isInstanceOf[Cvc5SolverContext])
    val rewriter = new SymbStateRewriterImpl(solver, new IncrementalRenaming(new IdleTracker), new ExprGradeStoreImpl)
    assert(rewriter.solverContext.asInstanceOf[RecordingSolverContext].solverImpl.isInstanceOf[Cvc5SolverContext])
    test(rewriter)
  }
}
