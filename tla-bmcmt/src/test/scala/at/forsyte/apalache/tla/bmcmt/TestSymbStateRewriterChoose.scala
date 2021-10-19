package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, SetT1, TestingPredefs}

trait TestSymbStateRewriterChoose extends RewriterBase with TestingPredefs {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "I" -> SetT1(IntT1())
  )

  test("""CHOOSE x \in {1, 2, 3}: x > 1""") { rewriterType: String =>
    val ex =
      choose(name("x") ? "i", enumSet(int(1), int(2), int(3)) ? "I", gt(name("x") ? "i", int(1)) ? "b")
        .typed(types, "i")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    def assertEq(i: Int): SymbState = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(eql(nextState.ex ? "i", int(i)).typed(types, "b")))
      solverContext.assertGroundExpr(ns.ex)
      ns
    }

    // in our implementation, CHOOSE is non-deterministic, so all three results below are possible
    rewriter.push()
    assertEq(3)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    assertEq(2)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    val ns = assertEq(1)
    assertUnsatOrExplain(rewriter, ns)
  }

  test("""CHOOSE x \in {1}: x > 1""") { rewriterType: String =>
    val ex = choose(name("x") ? "i", enumSet(int(1)) ? "I", gt(name("x"), int(1)) ? "b")
      .typed(types, "i")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())
  // The semantics of choose does not restrict the outcome on the empty sets,
  // so we do not test for anything here. Our previous implementation of CHOOSE produced default values in this case,
  // but this happened to be error-prone and sometimes conflicting with other rules. So, no default values.
  }

  test("""CHOOSE x \in {}: x > 1""") { rewriterType: String =>
    val ex = choose(name("x") ? "i", enumSet() ? "I", gt(name("x") ? "i", int(1)) ? "b")
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())

    def assertEq(i: Int): SymbState = {
      val eq = eql(nextState.ex ? "i", int(i))
        .typed(types, "b")
      val ns = rewriter.rewriteUntilDone(nextState.setRex(eq))
      solverContext.assertGroundExpr(ns.ex)
      ns
    }

    // Actually, semantics of choose does not restrict the outcome on the empty sets.
    // But we know that our implementation would always return 0 in this case.
    val ns = assertEq(1)
    assertUnsatOrExplain(rewriter, ns)
  }
}
