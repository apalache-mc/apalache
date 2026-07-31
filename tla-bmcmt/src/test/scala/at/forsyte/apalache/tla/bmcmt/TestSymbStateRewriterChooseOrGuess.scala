package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterChooseOrGuess extends RewriterBase {
  test("""CHOOSE x \in { 1, 2, 3 }: x > 1""") { rewriterType: SMTEncoding =>
    val cond = tla.gt(tla.name("x", IntT1), tla.int(1))
    val ex =
      tla.choose(tla.name("x", IntT1), tla.enumSet(tla.int(1), tla.int(2), tla.int(3)), cond)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(tla.unchecked(nextState.ex), tla.int(i))))
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
    val ex = tla.guess(tla.enumSet(tla.int(2), tla.int(3)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(tla.unchecked(nextState.ex), tla.int(i))))
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
    val cond = tla.gt(tla.name("x", IntT1), tla.int(1))
    val ex = tla.choose(tla.name("x", IntT1), tla.enumSet(tla.int(1)), cond)
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
    val cond = tla.gt(tla.name("x", IntT1), tla.int(1))
    val ex = tla.choose(tla.name("x", IntT1), tla.emptySet(IntT1), cond)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val eq = tla.eql(tla.unchecked(nextState.ex), tla.int(i))
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
    val ex = tla.guess(tla.emptySet(IntT1))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())

    def assertEq(i: Int): Unit = {
      val eq = tla.eql(tla.unchecked(nextState.ex), tla.int(i))
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
