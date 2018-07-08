package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.FailPredT
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterTlc extends RewriterBase {
  test("SE-TLC-PRINT: PRINT(...) -> TRUE") {
    val print = OperEx(TlcOper.print, tla.int(1), tla.str("hello"))
    val state = new SymbState(print,
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory() == nextStateRed.theory)
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())
        val failPreds = state.arena.findCellsByType(FailPredT())
        solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
        assert(!solverContext.sat()) // no failures should be registered

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-TLC-PRINT: PRINTT(...) -> TRUE") {
    val print = OperEx(TlcOper.printT, tla.str("hello"))
    val state = new SymbState(print,
      BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory() == nextStateRed.theory)
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())
        val failPreds = state.arena.findCellsByType(FailPredT())
        solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
        assert(!solverContext.sat()) // no failures should be registered

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-TLC-ASSERT: Assert(TRUE, _) -> TRUE") {
    val assertEx = OperEx(TlcOper.assert, tla.bool(true), tla.str("hello"))
    val state = new SymbState(assertEx, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory() == nextStateRed.theory)
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())
        val failPreds = nextStateRed.arena.findCellsByType(FailPredT())
        solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
        assert(!solverContext.sat()) // no failures should be registered

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-TLC-ASSERT: Assert(FALSE, _) -> TRUE") {
    val assertEx = OperEx(TlcOper.assert, tla.bool(false), tla.str("hello"))
    val state = new SymbState(assertEx, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case predEx@NameEx(name) =>
        assert(BoolTheory() == nextStateRed.theory)
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())
        val failPreds = nextStateRed.arena.findCellsByType(FailPredT())
        solverContext.assertGroundExpr(tla.or(failPreds.map(_.toNameEx): _*))
        assert(solverContext.sat()) // a failure should be registered

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
