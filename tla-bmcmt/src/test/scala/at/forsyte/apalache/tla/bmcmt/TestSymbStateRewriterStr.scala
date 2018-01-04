package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.values.TlaStr
import at.forsyte.apalache.tla.lir.{NameEx, ValEx}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterStr extends RewriterBase {
  test("SE-STR-CTOR: \"red\" -> $C$k") {
    val state = new SymbState(ValEx(TlaStr("red")),
      CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextStateRed = rewriter.rewriteUntilDone(state)
    nextStateRed.ex match {
      case predEx@NameEx(name) =>
        assert(CellTheory().hasConst(name))
        assert(CellTheory() == state.theory)
        assert(solverContext.sat())
        val redEqBlue = tla.eql(tla.str("blue"), tla.str("red"))
        val nextStateEq = rewriter.rewriteUntilDone(nextStateRed.setRex(redEqBlue))
        rewriter.push()
        solverContext.assertGroundExpr(nextStateEq.ex)
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(tla.not(nextStateEq.ex))
        assert(solverContext.sat())


      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
