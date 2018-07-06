package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.{NameEx, OperEx, TlaOperDecl}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterControl extends RewriterBase {
  test("""SE-ITE[1-4]: IF 3 > 2 THEN 2 < 4 ELSE 5 < 1 ~~> $C$k""") {
    val pred = tla.gt(tla.int(3), tla.int(2))
    val e1 = tla.lt(tla.int(2), tla.int(4))
    val e2 = tla.lt(tla.int(5), tla.int(1))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, BoolTheory(), arena, new Binding)
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

    val state = new SymbState(ite, BoolTheory(), arena, new Binding)
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

    val state = new SymbState(ite, IntTheory(), arena, new Binding)
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

    val state = new SymbState(ite, IntTheory(), arena, new Binding)
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

  test("""SE-ITE[5]: IF 3 < 2 THEN {1, 2} ELSE {2, 3} ~~> {2, 3}""") {
    val pred = tla.lt(tla.int(3), tla.int(2))
    val e1 = tla.enumSet(tla.int(1), tla.int(2))
    val e2 = tla.enumSet(tla.int(2), tla.int(3))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        rewriter.push()
        val eqState = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(tla.eql(res, e2)))
        solverContext.assertGroundExpr(eqState.ex)
        assert(solverContext.sat())
        rewriter.pop()
        val neqState = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(tla.eql(res, e1)))
        solverContext.assertGroundExpr(neqState.ex)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-ITE[5]: IF 2 < 3 THEN {1, 2} ELSE {2, 3} ~~> {1, 2}""") {
    val pred = tla.lt(tla.int(2), tla.int(3))
    val e1 = tla.enumSet(tla.int(1), tla.int(2))
    val e2 = tla.enumSet(tla.int(2), tla.int(3))
    val ite = tla.ite(pred, e1, e2)

    val state = new SymbState(ite, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(solverContext.sat())
        rewriter.push()
        val eqState = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(tla.eql(res, e1)))
        solverContext.assertGroundExpr(eqState.ex)
        assert(solverContext.sat())
        rewriter.pop()
        val neqState = rewriter.rewriteUntilDone(nextState.setTheory(BoolTheory()).setRex(tla.eql(res, e2)))
        solverContext.assertGroundExpr(neqState.ex)
        assert(!solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""LET A == TRUE IN... ~~> [A -> TRUE]""") {
    val decl = TlaOperDecl("A", List(), tla.bool(true))
    val letIn = tla.letIn(OperEx(decl.operator), decl)
    val state = new SymbState(letIn, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case res @ NameEx(name) =>
        assert(BoolTheory().hasConst(name))
        assert(name == solverContext.trueConst)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
