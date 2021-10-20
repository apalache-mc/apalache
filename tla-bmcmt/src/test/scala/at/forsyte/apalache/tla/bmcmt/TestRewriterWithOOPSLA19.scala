package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux._
import org.junit.runner.RunWith
import org.scalatest.Outcome
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestRewriterWithOOPSLA19
    extends TestCherryPick with TestSymbStateDecoder with TestSymbStateRewriter with TestSymbStateRewriterAction
    with TestSymbStateRewriterApalacheGen with TestSymbStateRewriterAssignment with TestSymbStateRewriterBool
    with TestSymbStateRewriterChoose with TestSymbStateRewriterControl with TestSymbStateRewriterExpand
    with TestSymbStateRewriterFiniteSets with TestSymbStateRewriterFoldSeq with TestSymbStateRewriterFoldSet
    with TestSymbStateRewriterFun with TestSymbStateRewriterFunSet with TestSymbStateRewriterInt
    with TestSymbStateRewriterPowerset with TestSymbStateRewriterRecFun with TestSymbStateRewriterRecord
    with TestSymbStateRewriterSequence with TestSymbStateRewriterSet with TestSymbStateRewriterStr
    with TestSymbStateRewriterTlc with TestSymbStateRewriterTuple with TestPropositionalOracle with TestSparseOracle
    with TestUninterpretedConstOracle {
  override protected def withFixture(test: OneArgTest): Outcome = {
    test("oopsla19")
  }
}
