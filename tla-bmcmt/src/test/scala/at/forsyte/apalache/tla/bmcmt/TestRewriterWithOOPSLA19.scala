package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.arena.PureArenaAdapter
import at.forsyte.apalache.tla.bmcmt.rules.aux._
import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRewriterWithOOPSLA19
    extends TestCherryPick with TestSymbStateDecoder with TestSymbStateRewriter with TestSymbStateRewriterAction
    with TestSymbStateRewriterApalacheGen with TestSymbStateRewriterAssignment with TestSymbStateRewriterBool
    with TestSymbStateRewriterChooseOrGuess with TestSymbStateRewriterControl with TestSymbStateRewriterExpand
    with TestSymbStateRewriterFiniteSets with TestSymbStateRewriterFoldSeq with TestSymbStateRewriterFoldSet
    with TestSymbStateRewriterFun with TestSymbStateRewriterFunSet with TestSymbStateRewriterInt
    with TestSymbStateRewriterPowerset with TestSymbStateRewriterRecord with TestSymbStateRewriterRowRecord
    with TestSymbStateRewriterVariant with TestSymbStateRewriterSequence with TestSymbStateRewriterSet
    with TestSymbStateRewriterStr with TestSymbStateRewriterTuple with TestPropositionalOracle with TestSparseOracle
    with TestUninterpretedConstOracle with TestSymbStateRewriterApalache with TestSymbStateRewriterMkSeq
    with TestDefaultValueFactory {
  override protected def withFixture(test: OneArgTest): Outcome = {
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true,
                smtEncoding = SMTEncoding.OOPSLA19)))
    arena = PureArenaAdapter.create(solverContext)
    val result = test(SMTEncoding.OOPSLA19)
    solverContext.dispose()
    result
  }
}
