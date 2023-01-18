package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.types.tla._

trait TestSymbStateRewriterChooseOrGuess extends RewriterBase {
  test("""CHOOSE x \in { 1, 2, 3 }: x > 1""") { rewriterType: SMTEncoding =>
    val cond = gt(name("x", IntT1), int(1))
    val ex =
      choose(name("x", IntT1), enumSet(int(1), int(2), int(3)), cond)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(eql(unchecked(nextState.ex), int(i))))
      solverContext.assertGroundExpr(ns.ex)
    }

    // in our implementation, CHOOSE is non-deterministic, so both 2 and 3 are possible choices
    rewriter.push()
    assertEq(3)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    assertEq(2)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    assertEq(1)
    assertUnsatOrExplain()
    rewriter.pop()
    // check that the default value (0) cannot be returned
    rewriter.push()
    assertEq(0)
    assertUnsatOrExplain()
  }

  test("""Guess({ 2, 3 })""") { rewriterType: SMTEncoding =>
    val ex = guess(enumSet(int(2), int(3)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(eql(unchecked(nextState.ex), int(i))))
      solverContext.assertGroundExpr(ns.ex)
    }

    // in our implementation, GUESS is non-deterministic, so both 2 and 3 are possible choices
    rewriter.push()
    assertEq(3)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    assertEq(2)
    assert(solverContext.sat())
  }

  test("""CHOOSE x \in { 1 }: x > 1""") { rewriterType: SMTEncoding =>
    val cond = gt(name("x", IntT1), int(1))
    val ex = choose(name("x", IntT1), enumSet(int(1)), cond)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())
  // The semantics of choose does not restrict the outcome on the empty sets,
  // so we do not test for anything here. Our previous implementation of CHOOSE produced default values in this case,
  // but this happened to be error-prone and sometimes conflicting with other rules. So, no default values.
  }

  test("""CHOOSE x \in {}: x > 1""") { rewriterType: SMTEncoding =>
    val cond = gt(name("x", IntT1), int(1))
    val ex = choose(name("x", IntT1), emptySet(IntT1), cond)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val eq = eql(unchecked(nextState.ex), int(i))
      val ns = rewriter.rewriteUntilDone(nextState.setRex(eq))
      solverContext.assertGroundExpr(ns.ex)
    }

    // Actually, semantics of choose does not restrict the outcome on the empty sets.
    // But we know that our implementation would always return 0 in this case.
    rewriter.push()
    assertEq(1)
    assertUnsatOrExplain()
    rewriter.pop()
    rewriter.push()
    assertEq(0)
    assert(solverContext.sat())
  }

  test("""Guess({})""") { rewriterType: SMTEncoding =>
    val ex = guess(emptySet(IntT1))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val eq = eql(unchecked(nextState.ex), int(i))
      val ns = rewriter.rewriteUntilDone(nextState.setRex(eq))
      solverContext.assertGroundExpr(ns.ex)
    }

    // Actually, semantics of GUESS does not restrict the outcome on the empty sets.
    // But we know that our implementation would always return 0 in this case.
    rewriter.push()
    assertEq(1)
    assertUnsatOrExplain()
    rewriter.pop()
    rewriter.push()
    assertEq(0)
    assert(solverContext.sat())
  }
}
