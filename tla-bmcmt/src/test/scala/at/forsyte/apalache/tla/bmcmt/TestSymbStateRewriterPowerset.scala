package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux.PowSetCtor
import at.forsyte.apalache.tla.bmcmt.types.{
  AnnotationParser,
  FinSetT,
  IntT,
  PowSetT
}
import at.forsyte.apalache.tla.lir.{NameEx, OperEx}
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.BmcOper
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterPowerset extends RewriterBase {
  test("""SE-SUBSET1: SUBSET {1, 2, 3} ~~> c_set""") {
    val ex = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
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
    val state = new SymbState(in, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""SE-SUBSET1: {} \in SUBSET {1, 2, 3}""") {
    // an empty set requires a type annotation
    val set12 =
      tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT())))
    val powset = tla.powSet(tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    val in = tla.in(set12, powset)
    val state = new SymbState(in, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""SE-SUBSET1: {1, 2, 3} \in SUBSET {1, 2, 3}""") {
    val set1to3 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val powset = tla.powSet(set1to3)
    val in = tla.in(set1to3, powset)
    val state = new SymbState(in, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""SE-SUBSET1: {1, 2, 3, 4} \in SUBSET {1, 2, 3}""") {
    def setTo(k: Int) = tla.enumSet(1 to k map tla.int: _*)

    val set1to4 = setTo(4)
    val powset = tla.powSet(setTo(3))
    val in = tla.in(set1to4, powset)
    val state = new SymbState(in, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(solverContext.sat())
  }

  test("""SE-SUBSET: \E X \in SUBSET {1, 2}: TRUE (sat)""") {
    // a regression test that failed in the previous versions
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val ex = tla.exists(tla.name("X"), tla.powSet(set), tla.bool(true))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    try {
      val nextState = rewriter.rewriteUntilDone(state)
      fail("expected an error message about unfolding a powerset")
    } catch {
      case _: UnsupportedOperationException => () // OK
    }
    //    nextState.ex match {
    //      case predEx@NameEx(name) =>
    //        assert(BoolTheory().hasConst(name))
    //        rewriter.push()
    //        solverContext.assertGroundExpr(predEx)
    //        assert(solverContext.sat())
    //        rewriter.pop()
    //        rewriter.push()
    //        solverContext.assertGroundExpr(tla.not(predEx))
    //        assertUnsatOrExplain(rewriter, nextState)
    //
    //      case _ =>
    //        fail("Unexpected rewriting result")
    //    }
  }

  test("""SE-SUBSET: Skolem(\E X \in SUBSET {1, 2}: TRUE) (sat)""") {
    // a regression test that failed in the previous versions
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val ex =
      OperEx(
        BmcOper.skolem,
        tla.exists(tla.name("X"), tla.powSet(set), tla.bool(true))
      )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET: Skolem(\E X \in SUBSET {1, 2}: FALSE (unsat))""") {
    // a regression test that failed in the previous versions
    val set = tla.enumSet(tla.int(1), tla.int(2))
    val ex =
      OperEx(
        BmcOper.skolem,
        tla.exists(tla.name("X"), tla.powSet(set), tla.bool(false))
      )

    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""PowSetCtor {1, 2}""") {
    val baseset = tla.enumSet(tla.int(1), tla.int(2))
    val state = new SymbState(baseset, arena, Binding())
    val rewriter = create()
    var nextState = rewriter.rewriteUntilDone(state)
    val baseCell = nextState.asCell
    nextState = new PowSetCtor(rewriter).confringo(nextState, baseCell)
    val powCell = nextState.asCell
    // give the cell type to type finder
    rewriter.typeFinder.reset(
      rewriter.typeFinder.varTypes + (powCell.toString -> powCell.cellType)
    )
    // check equality
    val eq = tla.eql(
      nextState.ex,
      tla.enumSet(
        tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT()))),
        tla.enumSet(tla.int(1)),
        tla.enumSet(tla.int(2)),
        tla.enumSet(tla.int(1), tla.int(2))
      )
    )
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

}
