package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.TlcOper
import at.forsyte.apalache.tla.lir._

trait TestSymbStateRewriterTlc extends RewriterBase {
  test("SE-TLC-PRINT: PRINT(...) -> TRUE") { rewriterType: String =>
    // Builder does not have a standard method for TLC!Print, as we do not construct internally
    val print = OperEx(TlcOper.print, int(1).typed(), str("hello").typed())(Typed(StrT1()))
    val state = new SymbState(print, arena, Binding())
    val rewriter = create(rewriterType)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case NameEx(_) =>
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-TLC-PRINT: PRINTT(...) -> TRUE") { rewriterType: String =>
    // Builder does not have a standard method for TLC!PrintT, as we do not construct internally
    val print = OperEx(TlcOper.printT, str("hello").typed())(Typed(StrT1()))
    val state = new SymbState(print, arena, Binding())
    val rewriter = create(rewriterType)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case NameEx(_) =>
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-TLC-ASSERT: Assert(TRUE, _) -> reach") { rewriterType: String =>
    // Builder does not have a standard method for TLC!Assert, as we do not construct internally
    val assertEx = OperEx(TlcOper.assert, bool(true).typed(), str("oops").typed())(Typed(BoolT1()))
    val state = new SymbState(assertEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case NameEx(_) =>
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-TLC-ASSERT: Assert(FALSE, _) -> TRUE") { rewriterType: String =>
    // Builder does not have a standard method for TLC!Assert, as we do not construct internally
    val assertEx = OperEx(TlcOper.assert, bool(false).typed(), str("oops").typed())(Typed(BoolT1()))
    val state = new SymbState(assertEx, arena, Binding())
    val rewriter = create(rewriterType)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case NameEx(_) =>
        solverContext.assertGroundExpr(nextStateRed.ex)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
