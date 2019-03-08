package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlaFunOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFiniteSets extends RewriterBase {
  test("""Cardinality({1, 2, 3}) = 3""") {
    val set = tla.enumSet(1.to(3).map(tla.int) :_*)
    val card = tla.card(set)
    val state = new SymbState(card, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.int(3), nextState.ex)))
  }

  test("""Cardinality({1, 2, 2, 2, 3, 3}) = 3""") {
    val set = tla.enumSet(Seq(1, 2, 2, 2, 3, 3).map(tla.int) :_*)
    val card = tla.card(set)
    val state = new SymbState(card, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.int(3), nextState.ex)))
  }

  test("""Cardinality({1, 2, 3} \ {2}) = 2""") {
    val set = tla.setminus(tla.enumSet(1.to(3).map(tla.int) :_*), tla.enumSet(tla.int(2)))
    val card = tla.card(set)
    val state = new SymbState(card, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.int(2), nextState.ex)))
  }

  test("""IsFiniteSet({1, 2, 3}) = TRUE""") {
    val set = tla.enumSet(1.to(3).map(tla.int) :_*)
    val card = tla.isFin(set)
    val state = new SymbState(card, CellTheory(), arena, new Binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.bool(true), nextState.ex)))
  }

}
