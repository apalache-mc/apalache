package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, IntT, PowSetT}
import at.forsyte.apalache.tla.lir.NameEx
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterPowerset extends RewriterBase {
  test("""SE-SUBSET1: SUBSET {1, 2, 3} ~~> c_set""") {
    val ex = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val state = new SymbState(ex, CellTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(CellTheory().hasConst(name))
        val cell = nextState.arena.findCellByNameEx(nextState.ex)
        assert(cell.cellType == PowSetT(FinSetT(IntT())))
        val dom = nextState.arena.getDom(cell)
        assert(dom.cellType == FinSetT(IntT()))
        val domElems = nextState.arena.getHas(dom)
        assert(domElems.length == 3)
        // the contents is tested in the rules below

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET1: {1, 2} \in SUBSET {1, 2, 3}""") {
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    val powset = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val in = tla.in(set12, powset)
    val state = new SymbState(in, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(nextState)
  }

  test("""SE-SUBSET1: {} \in SUBSET {1, 2, 3}""") {
    val set12 = tla.enumSet()
    val powset = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val in = tla.in(set12, powset)
    val state = new SymbState(in, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(nextState)
  }

  test("""SE-SUBSET1: {1, 2, 3} \in SUBSET {1, 2, 3}""") {
    val set1to3 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val powset = tla.powSet(set1to3)
    val in = tla.in(set1to3, powset)
    val state = new SymbState(in, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(nextState)
  }

  test("""SE-SUBSET1: {1, 2, 3, 4} \in SUBSET {1, 2, 3}""") {
    def setTo(k: Int) = tla.enumSet(1 to k map tla.int :_*)
    val set1to4 = setTo(4)
    val powset = tla.powSet(setTo(3))
    val in = tla.in(set1to4, powset)
    val state = new SymbState(in, BoolTheory(), arena, new Binding)
    val rewriter = new SymbStateRewriter(solverContext)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(nextState)
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(solverContext.sat())
  }
}
