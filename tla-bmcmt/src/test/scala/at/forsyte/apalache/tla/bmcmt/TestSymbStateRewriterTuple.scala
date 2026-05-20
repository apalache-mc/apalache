package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterTuple extends RewriterBase {
  test("""<<1, FALSE, {2}>>""") { rewriterType: SMTEncoding =>
    val tup = tla.tuple(tla.int(1), tla.bool(false), tla.enumSet(tla.int(2)))

    val state = new SymbState(tup, arena, Binding())
    val _ = create(rewriterType).rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test(""" <<1, FALSE, {2}>>[2] returns FALSE""") { rewriterType: SMTEncoding =>
    val tup = tla.tuple(tla.int(1), tla.bool(false), tla.enumSet(tla.int(2)))
    val tupleAcc = tla.app(tup, tla.int(2))
    val resEqFalse = tla.eql(tupleAcc, tla.bool(false))

    val state = new SymbState(resEqFalse, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""{<<1, FALSE>>, <<2, TRUE>>} works""") { rewriterType: SMTEncoding =>
    val tuple1 = tla.tuple(tla.int(1), tla.bool(false))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(true))
    val tupleSet = tla.enumSet(tuple1, tuple2)

    val state = new SymbState(tupleSet, arena, Binding())
    create(rewriterType).rewriteUntilDone(state)
    assert(solverContext.sat())
  }

  test("""~(<<2, FALSE>> = <<2, TRUE>>)""") { rewriterType: SMTEncoding =>
    val tuple1 = tla.tuple(tla.int(2), tla.bool(false))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(true))
    val eq = tla.not(tla.eql(tuple1, tuple2))

    val rewriter = create(rewriterType)
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""<<2, FALSE>> = <<2, FALSE>>""") { rewriterType: SMTEncoding =>
    val tuple1 = tla.tuple(tla.int(2), tla.bool(false))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(false))
    val eq = tla.eql(tuple1, tuple2)

    val rewriter = create(rewriterType)
    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(rewriter, state)
  }

  test("""DOMAIN <<2, FALSE, "c">> = {1, 2, 3}""") { rewriterType: SMTEncoding =>
    val tup = tla.tuple(tla.int(2), tla.bool(false), tla.str("c"))
    val set123 = tla.enumSet(1.to(3).map(i => tla.int(i)): _*)
    val eq = tla.eql(tla.dom(tup), set123)
    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state)
  }

  test("""[ <<1, FALSE>> EXCEPT ![1] = 3 ]""") { rewriterType: SMTEncoding =>
    val tup = tla.tuple(tla.int(1), tla.bool(false))
    val newTuple = tla.except(tup, tla.int(1), tla.int(3))
    val eq = tla.eql(newTuple, tla.tuple(tla.int(3), tla.bool(false)))

    val state = new SymbState(eq, arena, Binding())
    val rewriter = create(rewriterType)
    assertTlaExAndRestore(rewriter, state.setRex(eq))
  }
}
