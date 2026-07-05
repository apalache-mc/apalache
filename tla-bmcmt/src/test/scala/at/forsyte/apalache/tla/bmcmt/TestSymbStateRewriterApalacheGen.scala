package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.parser.DefaultType1Parser
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterApalacheGen extends RewriterBase {
  private val parser = DefaultType1Parser

  test("""Gen(1) for Int""") { rewriterType: SMTEncoding =>
    val gen = tla.gen(tla.int(1), IntT1)

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val ge10 = tla.ge(tla.unchecked(state.ex), tla.int(10))
    val nextState = rewriter.rewriteUntilDone(state.setRex(ge10))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(1) for Str""") { rewriterType: SMTEncoding =>
    val gen = tla.gen(tla.int(1), StrT1)

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val eq = tla.eql(tla.unchecked(state.ex), tla.str("foo"))
    val nextState = rewriter.rewriteUntilDone(state.setRex(eq))
    assert(solverContext.sat())
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assert(solverContext.sat())
  }

  test("""Gen(1) for ConstT1(name)""") { rewriterType: SMTEncoding =>
    // in the current implementation, ConstT1(PID) is generated the same way as StrT1
    val gen = tla.gen(tla.int(1), ConstT1("PID"))

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val eq = tla.eql(tla.unchecked(state.ex.withTag(Typed(StrT1))), tla.str("foo"))
    val nextState = rewriter.rewriteUntilDone(state.setRex(eq))
    assert(solverContext.sat())
    solverContext.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assert(solverContext.sat())
  }

  test("""Gen(1) for Bool""") { rewriterType: SMTEncoding =>
    val gen = tla.gen(tla.int(1), BoolT1)

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.push()
    // both b and ~b are possible
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    solverContext.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assert(solverContext.sat())
  }

  test("""Gen(3) = { 1, 2, 3 }""") { rewriterType: SMTEncoding =>
    val gen = tla.gen(tla.int(3), SetT1(IntT1))
    val eq123 = tla.eql(gen, tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))

    val state = new SymbState(eq123, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) = { }""") { rewriterType: SMTEncoding =>
    val gen = tla.gen(tla.int(3), SetT1(IntT1))
    val eq123 = tla.eql(gen, tla.emptySet(IntT1))

    val state = new SymbState(eq123, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for [i: Int, b: Bool]""") { rewriterType: SMTEncoding =>
    val recordT = parser("[ i: Int, b: Bool ]")
    val gen = tla.gen(tla.int(3), recordT)
    val i_eq_10 = tla.eql(tla.app(gen, tla.str("i")), tla.int(10))

    val state = new SymbState(i_eq_10, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for { i: Int, b: Bool }""") { rewriterType: SMTEncoding =>
    val recordT = parser("{ i: Int, b: Bool }")
    val gen = tla.gen(tla.int(3), recordT)
    val i_eq_10 = tla.eql(tla.app(gen, tla.str("i")), tla.int(10))

    val state = new SymbState(i_eq_10, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(3) for Foo(Int) | Bar(Bool)""") { rewriterType: SMTEncoding =>
    val variantT = parser("Foo(Int) | Bar(Bool)")
    val gen = tla.gen(tla.int(3), variantT)

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    // check that both options are possible
    val eqFoo = tla.eql(gen, tla.variant("Foo", tla.int(3), variantT.asInstanceOf[VariantT1]))
    val eqBar = tla.eql(gen, tla.variant("Bar", tla.bool(true), variantT.asInstanceOf[VariantT1]))
    // we do not check if-and-only-if, as every option is only possible but not required
    var nextState = rewriter.rewriteUntilDone(state.setRex(eqFoo))
    assert(solverContext.sat())
    nextState = rewriter.rewriteUntilDone(nextState.setRex(eqBar))
    assert(solverContext.sat())
  }

  test("""Gen(3) for <<Int, Bool>>""") { rewriterType: SMTEncoding =>
    val tupleType = TupT1(IntT1, BoolT1)
    val gen = tla.gen(tla.int(3), tupleType)
    val i_eq_10 = tla.eql(tla.app(gen, tla.int(1)), tla.int(10))

    val state = new SymbState(i_eq_10, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Gen(4) for Int -> Bool""") { rewriterType: SMTEncoding =>
    val funType = FunT1(IntT1, BoolT1)
    val gen = tla.gen(tla.int(4), funType)

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    val fun = tla.unchecked(nextState.ex)
    val dom_eq_1_3 = tla.eql(tla.dom(fun), tla.enumSet(tla.int(1), tla.int(3)))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom_eq_1_3))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    // make sure that the function does not return two different results for the argument
    val neq = tla.not(tla.eql(tla.app(fun, tla.int(1)), tla.app(fun, tla.minus(tla.int(2), tla.int(1)))))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(neq))
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Gen(4) for Seq(Bool)""") { rewriterType: SMTEncoding =>
    val seqType = SeqT1(BoolT1)
    val gen = tla.gen(tla.int(4), seqType)

    val state = new SymbState(gen, arena, Binding())
    val rewriter = create(rewriterType)
    var nextState = rewriter.rewriteUntilDone(state)
    val seq = tla.unchecked(nextState.ex)
    val dom_eq_123 = tla.eql(tla.dom(seq), tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))
    nextState = rewriter.rewriteUntilDone(nextState.setRex(dom_eq_123))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }
}
