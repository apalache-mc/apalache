package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.rules.aux.PowSetCtor
import at.forsyte.apalache.tla.bmcmt.types.{FinSetT, IntT, PowSetT}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, SetT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterPowerset extends RewriterBase {
  private val types = Map(
      "i" -> IntT1(),
      "I" -> SetT1(IntT1()),
      "II" -> SetT1(SetT1(IntT1())),
      "b" -> BoolT1()
  )

  test("""SUBSET {1, 2, 3}""") { rewriter: SymbStateRewriter =>
    val ex = powSet(enumSet(int(1), int(2), int(3)) ? "I")
      .typed(types, "II")
    val state = new SymbState(ex, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
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

  test("""SE-SUBSET1: {1, 2} \in SUBSET {1, 2, 3}""") { rewriter: SymbStateRewriter =>
    val set12 = enumSet(int(1), int(2)) ? "I"
    val powset = powSet(enumSet(int(1), int(2), int(3)) ? "I") ? "II"
    val inEx = in(set12, powset)
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SUBSET1: {} \in SUBSET {1, 2, 3}""") { rewriter: SymbStateRewriter =>
    // an empty set requires a type annotation
    val emptySet = enumSet()
      .typed(types, "I")
    val powset = powSet(enumSet(int(1), int(2), int(3)) ? "I") ? "II"
    val inEx = in(emptySet, powset)
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SUBSET1: {1, 2, 3} \in SUBSET {1, 2, 3}""") { rewriter: SymbStateRewriter =>
    val set1to3 = enumSet(int(1), int(2), int(3)) ? "I"
    val powset = powSet(set1to3) ? "II"
    val inEx = in(set1to3, powset)
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SUBSET1: {1, 2, 3, 4} \in SUBSET {1, 2, 3}""") { rewriter: SymbStateRewriter =>
    def setTo(k: Int) = enumSet(1 to k map int: _*)

    val set1to4 = setTo(4) ? "I"
    val powset = powSet(setTo(3) ? "I") ? "II"
    val inEx = not(in(set1to4, powset) ? "b")
      .typed(types, "b")
    val state = new SymbState(inEx, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SUBSET: \E X \in SUBSET {1, 2}: TRUE (sat)""") { rewriter: SymbStateRewriter =>
    // a regression test that failed in the previous versions
    val set = enumSet(int(1), int(2)) ? "I"
    val ex = exists(name("X") ? "I", powSet(set) ? "II", bool(true))
      .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    try {
      val _ = rewriter.rewriteUntilDone(state)
      fail("expected an error message about unfolding a powerset")
    } catch {
      case _: UnsupportedOperationException => () // OK
    }
  }

  test("""SE-SUBSET: Skolem(\E X \in SUBSET {1, 2}: TRUE) (sat)""") { rewriter: SymbStateRewriter =>
    // a regression test that failed in the previous versions
    val set = enumSet(int(1), int(2)) ? "I"
    val ex =
      apalacheSkolem(exists(name("X") ? "I", powSet(set) ? "II", bool(true)) ? "b")
        .typed(types, "b")
    val state = new SymbState(ex, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-SUBSET: Skolem(\E X \in SUBSET {1, 2}: FALSE (unsat))""") { rewriter: SymbStateRewriter =>
    // a regression test that failed in the previous versions
    val set = enumSet(int(1), int(2)) ? "I"
    val ex =
      apalacheSkolem(exists(name("X") ? "I", powSet(set) ? "II", bool(false)) ? "b")
        .typed(types, "b")

    val state = new SymbState(ex, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        rewriter.push()
        solverContext.assertGroundExpr(predEx)
        assertUnsatOrExplain(rewriter, nextState)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""PowSetCtor {1, 2}""") { rewriter: SymbStateRewriter =>
    val baseset = enumSet(int(1), int(2))
      .typed(types, "I")
    val state = new SymbState(baseset, arena, Binding())
    var nextState = rewriter.rewriteUntilDone(state)
    val baseCell = nextState.asCell
    nextState = new PowSetCtor(rewriter).confringo(nextState, baseCell)
    val powCell = nextState.asCell
    // check equality
    val eq = eql(nextState.ex,
        enumSet(enumSet() ? "I", enumSet(int(1)) ? "I", enumSet(int(2)) ? "I", enumSet(int(1), int(2)) ? "I") ? "II")
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

}
