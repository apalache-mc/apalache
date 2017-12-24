package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterControl extends RewriterBase {
  test("""SE-ITE[1-4]: IF 3 > 2 THEN 2 < 4 ELSE 5 < 1 ~~> $C$k""") {
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, BoolTheory(), arena, new Binding, solverContext)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(res)
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: IF 3 < 2 THEN 2 < 4 ELSE 5 < 1 ~~> $C$k""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, BoolTheory(), arena, new Binding, solverContext)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(tla.not(res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(res)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: IF 3 > 2 THEN 4 ELSE 1 ~~> $C$k""") {
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, IntTheory(), arena, new Binding, solverContext)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.int(4), res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(tla.int(1), res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[1-4]: IF 3 < 2 THEN 4 ELSE 1 ~~> $C$k""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.int(4)
    val e2 = tla.int(1)
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, IntTheory(), arena, new Binding, solverContext)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(IntTheory().hasConst(name))
        rewriter.push()
        solverContext.assertGroundExpr(tla.eql(tla.int(1), res))
        assert(solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.eql(tla.int(4), res))
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
