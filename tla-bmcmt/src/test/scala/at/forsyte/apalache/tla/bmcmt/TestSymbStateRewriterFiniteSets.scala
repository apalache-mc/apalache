package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, SetT1, TlaEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterFiniteSets extends RewriterBase {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "I" -> SetT1(IntT1())
  )

  test("""Cardinality({1, 2, 3}) = 3""") { rewriter: SymbStateRewriter =>
    val set = enumSet(1.to(3).map(int): _*)
    val cardinality = card(set ? "I")
      .typed(types, "i")
    val eq = eql(cardinality, int(3))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""Cardinality({1, 2, 2, 2, 3, 3}) = 3""") { rewriter: SymbStateRewriter =>
    val set = enumSet(Seq(1, 2, 2, 2, 3, 3).map(int): _*)
    val cardinality = card(set ? "I")
      .typed(types, "i")
    val eq = eql(cardinality, int(3))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 3}) >= 3)""") { rewriter: SymbStateRewriter =>
    val set = enumSet(1.to(3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(3)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 3}) >= 4)""") { rewriter: SymbStateRewriter =>
    val set = enumSet(1.to(3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(4)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 2, 3}) >= 4)""") { rewriter: SymbStateRewriter =>
    val set = enumSet(Seq(1, 2, 2, 3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(4)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 2, 3, 3}) >= 4)""") { rewriter: SymbStateRewriter =>
    val set = enumSet(Seq(1, 2, 2, 3, 3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(4)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({}) >= 0)""") { rewriter: SymbStateRewriter =>
    val set = enumSet()
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(0)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({}) >= 1)""") { rewriter: SymbStateRewriter =>
    val set = enumSet()
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(1)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({x \in {}: FALSE}) >= 0)""") { rewriter: SymbStateRewriter =>
    val set = filter(name("x") ? "i", enumSet() ? "I", bool(false))
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(0)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    // note that this optimization only works in the positive form. Its negation may be SAT.
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({x \in {}: FALSE}) >= 1)""") { rewriter: SymbStateRewriter =>
    val set = filter(name("x") ? "i", enumSet() ? "I", bool(false))
    val cardCmp = apalacheConstCard(ge(card(set ? "I") ? "i", int(1)) ? "b")
      .typed(types, "b")
    val state = new SymbState(cardCmp, arena, Binding())
    // note that this optimization only works in the positive form. Its negation may be SAT.
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Cardinality({1, 2, 3} \ {2}) = 2""") { rewriter: SymbStateRewriter =>
    def setminus(set: TlaEx, intVal: Int): TlaEx = {
      filter(name("t") ? "i", set ? "I", not(eql(name("t") ? "i", int(intVal)) ? "b") ? "b")
        .typed(types, "I")
    }

    val set = setminus(enumSet(1.to(3).map(int): _*).typed(types, "I"), 2)
    val cardinality = card(set ? "I")
    val eq = eql(cardinality ? "i", int(2))
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""IsFiniteSet({1, 2, 3}) = TRUE""") { rewriter: SymbStateRewriter =>
    val set = enumSet(1.to(3).map(int): _*)
    val isFiniteSet = isFin(set ? "I")
      .typed(types, "b")
    val state = new SymbState(isFiniteSet, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }
}
