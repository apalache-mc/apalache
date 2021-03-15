package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.typecheck.TypedPredefs._
import at.forsyte.apalache.tla.pp.{Keramelizer, UniqueNameGenerator}
import at.forsyte.apalache.tla.typecheck.{BoolT1, IntT1, SetT1}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

/**
 * Tests for the TLA+ operators that are deal with by rewriting into KerA+.
 * Although they are not needed to test the rewriting rules, we keep them for regression.
 *
 * @author Igor Konnov
 */
@RunWith(classOf[JUnitRunner])
class TestRewriterKeraSet extends RewriterBase with TestingPredefs {
  private var keramelizer = new Keramelizer(new UniqueNameGenerator, TrackerWithListeners())

  test("""SE-SET-CAP[1-2]: {1, 3} \cap {3, 4} = {3}""") {
    val types = Map("S" -> SetT1(IntT1()), "i" -> IntT1())
    val left = tla.enumSet(tla.int(1), tla.int(3))
    val right = tla.enumSet(tla.int(3), tla.int(4))
    val expected = tla
      .enumSet(tla.int(3))
      .typed(types, "S")
    val intersection = tla
      .cap(left ? "S", right ? "S")
      .typed(types, "S")
    val capSet = keramelizer.transform(intersection)
    val eqExpected = tla.eql(capSet, expected).typed(BoolT1())

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SET-DIFF[1-2]: {1, 3, 5} \cap {1, 4} = {3, 5}""") {
    val types = Map("S" -> SetT1(IntT1()), "i" -> IntT1())
    val left = tla.enumSet(tla.int(1), tla.int(3), tla.int(5)) ? "S"
    val right = tla.enumSet(tla.int(1), tla.int(4)) ? "S"
    val expected = tla
      .enumSet(tla.int(3), tla.int(5))
      .typed(types, "S")
    val diff = tla
      .setminus(left, right)
      .typed(types, "S")
    val minusSet = keramelizer.transform(diff)
    val eqExpected = tla
      .eql(minusSet, expected)
      .typed(BoolT1())

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SET-CUP: regression""") {
    val types = Map("S" -> SetT1(IntT1()), "i" -> IntT1())
    // 2019-01-18, Igor: this bug originally appeared in TwoPhase.tla, the MWE can be found in Bug20190118.tla
    // S = {1} \ {1}
    val set1 = tla.setminus(tla.enumSet(tla.int(1)) ? "S", tla.enumSet(tla.int(1)) ? "S") ? "S"
    // T = {3} \ 3
    val set2 = tla.setminus(tla.enumSet(tla.int(3)) ? "S", tla.enumSet(tla.int(3)) ? "S") ? "S"
    // R = S \cup T = {}
    // the buggy implementation will try in(1, T) and this may return true!
    val set3 = tla
      .cup(set1, set2)
      .typed(types, "S")
    val membership = tla
      .in(tla.int(1), set3)
      .typed(BoolT1())
    val trans = keramelizer.transform(membership)
    val state = new SymbState(trans, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    // the buggy implementation had: 1 \ in R
    assertUnsatOrExplain(rewriter, nextState)
  }

}
