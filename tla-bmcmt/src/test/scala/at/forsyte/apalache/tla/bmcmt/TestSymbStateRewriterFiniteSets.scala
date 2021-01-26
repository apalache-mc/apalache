package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.{OperEx, TlaEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFiniteSets extends RewriterBase {
  test("""Cardinality({1, 2, 3}) = 3""") {
    val set = tla.enumSet(1.to(3).map(tla.int): _*)
    val card = tla.card(set)
    val state = new SymbState(card, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(tla.int(3), nextState.ex))
    )
  }

  test("""Cardinality({1, 2, 2, 2, 3, 3}) = 3""") {
    val set = tla.enumSet(Seq(1, 2, 2, 2, 3, 3).map(tla.int): _*)
    val card = tla.card(set)
    val state = new SymbState(card, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(tla.int(3), nextState.ex))
    )
  }

  test("""BMC!ConstCard(Cardinality({1, 2, 3}) >= 3)""") {
    val set = tla.enumSet(1.to(3).map(tla.int): _*)
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(3)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({1, 2, 3}) >= 4)""") {
    val set = tla.enumSet(1.to(3).map(tla.int): _*)
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(4)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({1, 2, 2, 3}) >= 4)""") {
    val set = tla.enumSet(List(1, 2, 2, 3).map(tla.int): _*)
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(4)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({1, 2, 2, 3, 3}) >= 4)""") {
    val set = tla.enumSet(List(1, 2, 2, 3).map(tla.int): _*)
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(4)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({}) >= 0)""") {
    val set = tla.enumSet()
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(0)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({x \in {}: FALSE}) >= 0)""") {
    val set = tla.filter(tla.name("x"), tla.enumSet(), tla.bool(false))
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(0)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({x \in {}: FALSE}) >= 1)""") {
    val set = tla.filter(tla.name("x"), tla.enumSet(), tla.bool(false))
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(1)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""BMC!ConstCard(Cardinality({}) >= 1)""") {
    val set = tla.enumSet()
    val cardCmp = OperEx(BmcOper.constCard, tla.ge(tla.card(set), tla.int(1)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Cardinality({1, 2, 3} \ {2}) = 2""") {
    def setminus(set: TlaEx, intVal: Int): TlaEx = {
      tla.filter(
        tla.name("t"),
        set,
        tla.not(tla.eql(tla.name("t"), tla.int(intVal)))
      )
    }

    val set = setminus(tla.enumSet(1.to(3).map(tla.int): _*), 2)
    val card = tla.card(set)
    val state = new SymbState(card, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(tla.int(2), nextState.ex))
    )
  }

  test("""IsFiniteSet({1, 2, 3}) = TRUE""") {
    val set = tla.enumSet(1.to(3).map(tla.int): _*)
    val card = tla.isFin(set)
    val state = new SymbState(card, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(tla.bool(true), nextState.ex))
    )
  }

}
