package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.{SMTEncoding, SMTSolver}
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.rules.aux._
import at.forsyte.apalache.tla.bmcmt.smt.{Cvc5SolverContext, PreproSolverContext, SolverConfig}
import org.scalatest.Outcome

class TestRewriterWithCvc5OOPSLA19
    extends TestCherryPick with TestSymbStateDecoder with TestSymbStateRewriter with TestSymbStateRewriterAction
    with TestSymbStateRewriterApalacheGen with TestSymbStateRewriterAssignment with TestSymbStateRewriterBool
    with TestSymbStateRewriterChooseOrGuess with TestSymbStateRewriterControl with TestSymbStateRewriterExpand
    with TestSymbStateRewriterFiniteSets with TestSymbStateRewriterFoldSeq with TestSymbStateRewriterFoldSet
    with TestSymbStateRewriterFun with TestSymbStateRewriterFunSet with TestSymbStateRewriterInt
    with TestSymbStateRewriterPowerset with TestSymbStateRewriterRecord with TestSymbStateRewriterRowRecord
    with TestSymbStateRewriterVariant with TestSymbStateRewriterSequence with TestSymbStateRewriterSet
    with TestSymbStateRewriterStr with TestSymbStateRewriterTuple with TestPropositionalOracle with TestSparseOracle
    with TestUninterpretedConstOracle with TestSymbStateRewriterApalache with TestSymbStateRewriterMkSeq
    with TestDefaultValueFactory with TestSymbStateRewriterRepeat {
  override protected def withFixture(test: OneArgTest): Outcome = {
    solverContext = new PreproSolverContext(new Cvc5SolverContext(SolverConfig.default.copy(debug = true,
                smtEncoding = SMTEncoding.OOPSLA19, smtSolver = SMTSolver.CVC5)))
    arena = PureArenaAdapter.create(solverContext)
    val rewriter = create(SMTEncoding.OOPSLA19)
    assert(rewriter.solverContext.config.smtSolver == SMTSolver.CVC5)
    val result = test(SMTEncoding.OOPSLA19)
    solverContext.dispose()
    result
  }
}
