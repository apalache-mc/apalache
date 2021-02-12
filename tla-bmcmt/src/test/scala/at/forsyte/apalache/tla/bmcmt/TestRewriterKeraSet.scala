package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience._
import at.forsyte.apalache.tla.lir.oper.TlaSetOper
import at.forsyte.apalache.tla.lir.transformations.impl.TrackerWithListeners
import at.forsyte.apalache.tla.lir.UntypedPredefs._
import at.forsyte.apalache.tla.pp.{Keramelizer, UniqueNameGenerator}

/**
 * Tests for the TLA+ operators that are deal with by rewriting into KerA+.
 * Although they are not needed to test the rewriting rules, we keep them for regression.
 *
 * @author Igor Konnov
 */
class TestRewriterKeraSet extends RewriterBase with TestingPredefs {
  private var keramelizer = new Keramelizer(new UniqueNameGenerator, TrackerWithListeners())

  test("""SE-SET-CAP[1-2]: {1, 3} \cap {3, 4} = {3}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = tla.enumSet(tla.int(1), tla.int(3))
    val right = tla.enumSet(tla.int(3), tla.int(4))
    val expected = tla.enumSet(tla.int(3))
    val capSet = keramelizer.transform(tla.cap(left, right))
    val eqExpected = tla.eql(capSet, expected)

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SET-DIFF[1-2]: {1, 3, 5} \cap {1, 4} = {3, 5}""") {
    def mkSet(elems: TlaEx*) = OperEx(TlaSetOper.enumSet, elems: _*)

    val left = tla.enumSet(tla.int(1), tla.int(3), tla.int(5))
    val right = tla.enumSet(tla.int(1), tla.int(4))
    val expected = tla.enumSet(tla.int(3), tla.int(5))
    val minusSet = keramelizer.transform(tla.setminus(left, right))
    val eqExpected = tla.eql(minusSet, expected)

    val state = new SymbState(eqExpected, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""SE-SET-CUP: regression""") {
    // 2019-01-18, Igor: this bug originally appeared in TwoPhase.tla, the MWE can be found in Bug20190118.tla
    // S = {1} \ {1}
    val set1 = tla.setminus(tla.enumSet(tla.int(1)), tla.enumSet(tla.int(1)))
    // T = {3} \ 3
    val set2 = tla.setminus(tla.enumSet(tla.int(3)), tla.enumSet(tla.int(3)))
    // R = S \cup T = {}
    val set3 = tla.cup(set1, set2) // the buggy implementation will try in(1, T) and this may return true!
    val trans = keramelizer.transform(tla.in(tla.int(1), set3))
    val state = new SymbState(trans, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    solverContext.assertGroundExpr(nextState.ex)
    // the buggy implementation had: 1 \ in R
    assertUnsatOrExplain(rewriter, nextState)
  }

}
