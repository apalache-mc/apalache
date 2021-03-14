package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{AnnotationParser, FinSetT, IntT}
import at.forsyte.apalache.tla.lir.TestingPredefs
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterChoose extends RewriterBase with TestingPredefs {
  test("""CHOOSE x \in {1, 2, 3}: x > 1""") {
    val ex =
      tla.choose(tla.name("x"), tla.enumSet(tla.int(1), tla.int(2), tla.int(3)), tla.gt(tla.name("x"), tla.int(1)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    def assertEq(i: Int): SymbState = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(nextState.ex, tla.int(i))))
      solverContext.assertGroundExpr(ns.ex)
      ns
    }

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

  test("""CHOOSE x \in {1}: x > 1""") {
    val ex = tla.choose(tla.name("x"), tla.enumSet(tla.int(1)), tla.gt(tla.name("x"), tla.int(1)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())
    // The semantics of choose does not restrict the outcome on the empty sets,
    // so we do not test for anything here. Our previous implementation of CHOOSE produced default values in this case,
    // but this happened to be error-prone and sometimes conflicting with other rules. So, no default values.
  }

  test("""CHOOSE x \in {}: x > 1""") {
    val ex = tla.choose(tla.name("x"), tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT()))),
        tla.gt(tla.name("x"), tla.int(1)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    // the buggy implementation of choose fails on a dynamically empty set
    assert(solverContext.sat())
    def assertEq(i: Int): SymbState = {
      val ns = rewriter.rewriteUntilDone(nextState.setRex(tla.eql(nextState.ex, tla.int(i))))
      solverContext.assertGroundExpr(ns.ex)
      ns
    }

    // Actually, semantics of choose does not restrict the outcome on the empty sets.
    // But we know that our implementation would always return 0 in this case.
    val ns = assertEq(1)
    assertUnsatOrExplain(rewriter, ns)
  }
}
