package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux._
import at.forsyte.apalache.tla.bmcmt.smt.{PreproSolverContext, SolverConfig, Z3SolverContext}
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatestplus.junit.JUnitRunner

// TODO: add TestSymbStateRewriterSequence, TestSymbStateRewriterApalache, and TestSymbStateRewriterApalacheGen

@RunWith(classOf[JUnitRunner])
class TestRewriterWithArrays
    extends TestCherryPick with TestSymbStateDecoder with TestSymbStateRewriter with TestSymbStateRewriterAction
    with TestSymbStateRewriterAssignment with TestSymbStateRewriterBool with TestSymbStateRewriterChoose
    with TestSymbStateRewriterControl with TestSymbStateRewriterExpand with TestSymbStateRewriterFiniteSets
    with TestSymbStateRewriterFoldSeq with TestSymbStateRewriterFoldSet with TestSymbStateRewriterFun
    with TestSymbStateRewriterFunSet with TestSymbStateRewriterInt with TestSymbStateRewriterPowerset
    with TestSymbStateRewriterRecFun with TestSymbStateRewriterRecord with TestSymbStateRewriterSet
    with TestSymbStateRewriterStr with TestSymbStateRewriterTuple with TestPropositionalOracle with TestSparseOracle
    with TestUninterpretedConstOracle {
  override protected def withFixture(test: OneArgTest): Outcome = {
    solverContext = new PreproSolverContext(new Z3SolverContext(SolverConfig.default.copy(debug = true,
                smtEncoding = arraysEncoding)))
    arena = Arena.create(solverContext)
    val result = test(arraysEncoding)
    solverContext.dispose()
    result
  }
}
