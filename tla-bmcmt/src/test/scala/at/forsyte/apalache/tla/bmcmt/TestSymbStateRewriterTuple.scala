package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, NameEx, SetT1, StrT1, TupT1}
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterTuple extends RewriterBase {
  private val types = Map(
      "b" -> BoolT1(),
      "i" -> IntT1(),
      "(i)" -> TupT1(IntT1()),
      "I" -> SetT1(IntT1()),
      "ib" -> TupT1(IntT1(), BoolT1()),
      "ibs" -> TupT1(IntT1(), BoolT1(), StrT1()),
      "IB" -> SetT1(TupT1(IntT1(), BoolT1())),
      "ibI" -> TupT1(IntT1(), BoolT1(), SetT1(IntT1()))
  )

  test("""<<1, FALSE, {2}>>""") {
    val tup = tuple(int(1), bool(false), enumSet(int(2)) ? "I")
      .typed(types, "ibI")

    val state = new SymbState(tup, arena, Binding())
    val _ = create().rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test(""" <<1, FALSE, {2}>>[2] returns FALSE""") {
    val tup = tuple(int(1), bool(false), enumSet(int(2)) ? "I")
    val tupleAcc = appFun(tup ? "ibI", int(2))
      .typed(types, "b")
    val resEqFalse = eql(tupleAcc, bool(false))
      .typed(BoolT1())

    val state = new SymbState(resEqFalse, arena, Binding())
    assertTlaExAndRestore(create(), state)
  }

  test("""{<<1, FALSE>>, <<2, TRUE>>} works""") {
    val tuple1 = tuple(int(1), bool(false))
    val tuple2 = tuple(int(2), bool(true))
    val tupleSet = enumSet(tuple1 ? "ib", tuple2 ? "ib")
      .typed(types, "IB")

    val state = new SymbState(tupleSet, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""~(<<2, FALSE>> = <<2, TRUE>>)""") {
    val tuple1 = tuple(int(2), bool(false))
    val tuple2 = tuple(int(2), bool(true))
    val eq = not(eql(tuple1 ? "ib", tuple2 ? "ib") ? "b")
      .typed(types, "b")

    val rewriter = create()
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""<<2, FALSE>> = <<2, FALSE>>""") {
    val tuple1 = tuple(int(2), bool(false))
    val tuple2 = tuple(int(2), bool(false))
    val eq = eql(tuple1 ? "ib", tuple2 ? "ib")
      .typed(types, "b")

    val rewriter = create()
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN <<2, FALSE, "c">> = {1, 2, 3}""") {
    val tup = tuple(int(2), bool(false), str("c"))
    val set123 = enumSet(1.to(3) map int: _*)
    val eq = eql(dom(tup ? "ibs") ? "I", set123 ? "I")
      .typed(types, "b")
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[ <<1, FALSE>> EXCEPT ![1] = 3 ]""") {
    val tup = tuple(int(1), bool(false))
    val newTuple = except(tup ? "ib", tuple(int(1)) ? "(i)", int(3))
      .typed(types, "ib")
    val eq = eql(newTuple, tuple(int(3), bool(false)) ? "ib")
      .typed(types, "b")

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create()
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }
}
