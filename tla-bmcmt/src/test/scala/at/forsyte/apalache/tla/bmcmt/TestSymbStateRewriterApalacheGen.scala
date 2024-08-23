package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.{tla => tlaLegacy}
import at.forsyte.apalache.tla.lir.oper.ApalacheOper
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.types.tlaU._
import at.forsyte.apalache.tla.typecomp._

trait TestSymbStateRewriterApalacheGen extends RewriterBase {
  private val parser = DefaultType1Parser

  test("""Gen(1) for Int""") { rewriterType: SMTEncoding =>
    val gen = OperEx(ApalacheOper.gen, int(1))(Typed(IntT1))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val ge10 = ge(unchecked(state.ex), int(10))
    val nextState = rewriter.rewriteUntilDone(state.setRex(ge10))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(1) for Str""") { rewriterType: SMTEncoding =>
    val gen = OperEx(ApalacheOper.gen, int(1))(Typed(StrT1))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val eq = eql(unchecked(state.ex), str("foo"))
    val nextState = rewriter.rewriteUntilDone(state.setRex(eq))
    assert(solverContext.sat())
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(tlaLegacy.not(nextState.ex).as(BoolT1))
    assert(solverContext.sat())
  }

  test("""Gen(1) for ConstT1(name)""") { rewriterType: SMTEncoding =>
    // in the current implementation, ConstT1(PID) is generated the same way as StrT1
    val gen = OperEx(ApalacheOper.gen, int(1))(Typed(ConstT1("PID")))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val eq = tlaLegacy.eql(state.ex.as(StrT1), tlaLegacy.str("foo")).as(BoolT1)
    val nextState = rewriter.rewriteUntilDone(state.setRex(eq))
    assert(solverContext.sat())
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(tlaLegacy.not(nextState.ex).as(BoolT1))
    assert(solverContext.sat())
  }

  test("""Gen(1) for Bool""") { rewriterType: SMTEncoding =>
    val gen = OperEx(ApalacheOper.gen, int(1))(Typed(BoolT1))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.push()
    // both b and ~b are possible
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(not(unchecked(nextState.ex)))
    assert(solverContext.sat())
  }

  test("""Gen(3) = { 1, 2, 3 }""") { rewriterType: SMTEncoding =>
    val gen = unchecked(OperEx(ApalacheOper.gen, int(3))(Typed(SetT1(IntT1))))
    val eq123 = eql(gen, enumSet(int(1), int(2), int(3)))

    val state = new SymbState(eq123, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) = { }""") { rewriterType: SMTEncoding =>
    val gen = unchecked(OperEx(ApalacheOper.gen, int(3))(Typed(SetT1(IntT1))))
    val eq123 = eql(gen, emptySet(IntT1))

    val state = new SymbState(eq123, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for [i: Int, b: Bool]""") { rewriterType: SMTEncoding =>
    val recordT = parser("[ i: Int, b: Bool ]")
    val gen = unchecked(OperEx(ApalacheOper.gen, int(3))(Typed(recordT)))
    val i_eq_10 = eql(app(gen, str("i")), int(10))

    val state = new SymbState(i_eq_10, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for { i: Int, b: Bool }""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ i: Int, b: Bool }")
    val gen = unchecked(OperEx(ApalacheOper.gen, int(3))(Typed(recordT)))
    val i_eq_10 = eql(app(gen, str("i")), int(10))

    val state = new SymbState(i_eq_10, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for Foo(Int) | Bar(Bool)""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val gen = unchecked(OperEx(ApalacheOper.gen, int(3))(Typed(variantT)))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    // check that both options are possible
    val eqFoo = eql(gen, unchecked(tlaLegacy.variant("Foo", int(3).build).as(variantT)))
    val eqBar = eql(gen, unchecked(tlaLegacy.variant("Bar", bool(true).build).as(variantT)))
    // we do not check if-and-only-if, as every option is only possible but not required
    var nextState = rewriter.rewriteUntilDone(state.setRex(eqFoo))
    assert(solverContext.sat())
    nextState = rewriter.rewriteUntilDone(nextState.setRex(eqBar))
    assert(solverContext.sat())
  }

  test("""Gen(3) for <<Int, Bool>>""") { rewriterType: SMTEncoding =>
    val tupleType = TupT1(IntT1, BoolT1)
    val gen = OperEx(ApalacheOper.gen, int(3))(Typed(tupleType))
    val i_eq_10 = eql(app(unchecked(gen), int(1)), int(10))

    val state = new SymbState(i_eq_10, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(4) for Int -> Bool""") { rewriterType: SMTEncoding =>
    val funType = FunT1(IntT1, BoolT1)
    val gen = OperEx(ApalacheOper.gen, int(4))(Typed(funType))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    val fun = unchecked(nextState.ex)
    val dom_eq_1_3 = eql(dom(fun), enumSet(int(1), int(3)))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom_eq_1_3))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    // make sure that the function does not return two different results for the argument
    val neq = not(eql(app(fun, int(1)), app(fun, minus(int(2), int(1)))))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(neq))
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Gen(4) for Seq(Bool)""") { rewriterType: SMTEncoding =>
    val seqType = SeqT1(BoolT1)
    val gen = OperEx(ApalacheOper.gen, int(4))(Typed(seqType))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    val seq = unchecked(nextState.ex)
    val dom_eq_123 = eql(dom(seq), enumSet(int(1), int(2), int(3)))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom_eq_123))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }
}
