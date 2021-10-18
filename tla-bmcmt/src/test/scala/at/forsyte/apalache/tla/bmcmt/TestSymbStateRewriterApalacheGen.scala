package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.lir.{BoolT1, ConstT1, FunT1, IntT1, OperEx, RecT1, SeqT1, SetT1, StrT1, TupT1, Typed}
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterApalacheGen extends RewriterBase {
  private val types = Map("i" -> IntT1(), "I" -> SetT1(IntT1()), "b" -> BoolT1(), "s" -> StrT1())

  test("""Gen(1) for Int""") { rewriter: SymbStateRewriter =>
    val gen = OperEx(ApalacheOper.gen, int(1).typed())(Typed(IntT1()))

    val state = new SymbState(gen, arena, Binding())
    val ge10 = ge(state.ex ? "i", int(10))
      .typed(types, "b")
    val nextState = rewriter.rewriteUntilDone(state.setRex(ge10))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(1) for Str""") { rewriter: SymbStateRewriter =>
    val gen = OperEx(ApalacheOper.gen, int(1).typed())(Typed(StrT1()))

    val state = new SymbState(gen, arena, Binding())
    val eq = eql(state.ex ? "s", str("foo"))
      .typed(types, "b")
    val nextState = rewriter.rewriteUntilDone(state.setRex(eq))
    assert(solverContext.sat())
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(not(nextState.ex ? "b").typed(types, "b"))
    assert(solverContext.sat())
  }

  test("""Gen(1) for ConstT1(name)""") { rewriter: SymbStateRewriter =>
    // in the current implementation, ConstT1(PID) is generated the same way as StrT1
    val gen = OperEx(ApalacheOper.gen, int(1).typed())(Typed(ConstT1("PID")))

    val state = new SymbState(gen, arena, Binding())
    val eq = eql(state.ex ? "s", str("foo"))
      .typed(types, "b")
    val nextState = rewriter.rewriteUntilDone(state.setRex(eq))
    assert(solverContext.sat())
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(not(nextState.ex ? "b").typed(types, "b"))
    assert(solverContext.sat())
  }

  test("""Gen(1) for Bool""") { rewriter: SymbStateRewriter =>
    val gen = OperEx(ApalacheOper.gen, int(1).typed())(Typed(BoolT1()))

    val state = new SymbState(gen, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.push()
    // both b and ~b are possible
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(not(nextState.ex ? "b").typed(types, "b"))
    assert(solverContext.sat())
  }

  test("""Gen(3) = { 1, 2, 3 }""") { rewriter: SymbStateRewriter =>
    val gen = OperEx(ApalacheOper.gen, int(3).typed())(Typed(SetT1(IntT1())))
    val eq123 = eql(gen, enumSet(int(1), int(2), int(3)) ? "I").typed(types, "b")

    val state = new SymbState(eq123, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) = { }""") { rewriter: SymbStateRewriter =>
    val gen = OperEx(ApalacheOper.gen, int(3).typed())(Typed(SetT1(IntT1())))
    val eq123 = eql(gen, enumSet() ? "I").typed(types, "b")

    val state = new SymbState(eq123, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for [i: Int, b: Bool]""") { rewriter: SymbStateRewriter =>
    val recordType = RecT1("i" -> IntT1(), "b" -> BoolT1())
    val gen = OperEx(ApalacheOper.gen, int(3).typed())(Typed(recordType))
    val i_eq_10 = eql(appFun(gen, str("i")) ? "i", int(10)).typed(types, "b")

    val state = new SymbState(i_eq_10, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for <<Int, Bool>>""") { rewriter: SymbStateRewriter =>
    val tupleType = TupT1(IntT1(), BoolT1())
    val gen = OperEx(ApalacheOper.gen, int(3).typed())(Typed(tupleType))
    val i_eq_10 = eql(appFun(gen, int(1)) ? "i", int(10)).typed(types, "b")

    val state = new SymbState(i_eq_10, arena, Binding())
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(4) for Int -> Bool""") { rewriter: SymbStateRewriter =>
    val funType = FunT1(IntT1(), BoolT1())
    val gen = OperEx(ApalacheOper.gen, int(4).typed())(Typed(funType))

    val state = new SymbState(gen, arena, Binding())
    var nextState = rewriter.rewriteUntilDone(state)
    val fun = nextState.ex
    val dom_eq_1_3 = eql(dom(fun) ? "I", enumSet(int(1), int(3)) ? "I")
      .typed(types, "b")
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom_eq_1_3))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    // make sure that the function does not return two different results for the argument
    val neq = not(eql(appFun(fun, int(1)) ? "b", appFun(fun, minus(int(2), int(1)) ? "i") ? "b") ? "b")
      .typed(types, "b")
    nextState = rewriter.rewriteUntilDone(nextState.setRex(neq))
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Gen(4) for Seq(Bool)""") { rewriter: SymbStateRewriter =>
    val seqType = SeqT1(BoolT1())
    val gen = OperEx(ApalacheOper.gen, int(4).typed())(Typed(seqType))

    val state = new SymbState(gen, arena, Binding())
    var nextState = rewriter.rewriteUntilDone(state)
    val seq = nextState.ex
    val dom_eq_123 = eql(dom(seq) ? "I", enumSet(int(1), int(2), int(3)) ? "I")
      .typed(types, "b")
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom_eq_123))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())

  }
}
