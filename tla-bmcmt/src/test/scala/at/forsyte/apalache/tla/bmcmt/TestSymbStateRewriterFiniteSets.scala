package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.IntT1
import at.forsyte.apalache.tla.pp.TlaInputError
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterFiniteSets extends RewriterBase {
  test("""Cardinality({1, 2, 3}) = 3""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(1.to(3).map(i => tla.int(i)): _*)
    val cardinality = tla.cardinality(set)
    val eq = tla.eql(cardinality, tla.int(3))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Cardinality(SUBSET {1, 2}) throws""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(1.to(2).map(i => tla.int(i)): _*)
    val powerset = tla.powSet(set)
    val cardinality = tla.cardinality(powerset)

    val state = new SymbState(cardinality, arena, Binding())
    assertThrows[TlaInputError] {
      // this case should be handled by preprocessing
      create(rewriterType).rewriteUntilDone(state)
    }
  }

  test("""Cardinality({1, 2, 2, 2, 3, 3}) = 3""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(Seq(1, 2, 2, 2, 3, 3).map(i => tla.int(i)): _*)
    val cardinality = tla.cardinality(set)
    val eq = tla.eql(cardinality, tla.int(3))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 3}) >= 3)""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(1.to(3).map(i => tla.int(i)): _*)
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(3)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 3}) >= 4)""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(1.to(3).map(i => tla.int(i)): _*)
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(4)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 2, 3}) >= 4)""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(Seq(1, 2, 2, 3).map(i => tla.int(i)): _*)
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(4)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 2, 3, 3}) >= 4)""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(Seq(1, 2, 2, 3, 3).map(i => tla.int(i)): _*)
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(4)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({}) >= 0)""") { rewriterType: SMTEncoding =>
    val set = tla.emptySet(IntT1)
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(0)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({}) >= 1)""") { rewriterType: SMTEncoding =>
    val set = tla.emptySet(IntT1)
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(1)))
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({x \in {}: FALSE}) >= 0)""") { rewriterType: SMTEncoding =>
    val set = tla.filter(tla.name("x", IntT1), tla.emptySet(IntT1), tla.bool(false))
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(0)))
    val state = new SymbState(cardCmp, arena, Binding())
    // note that this optimization only works in the positive form. Its negation may be SAT.
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({x \in {}: FALSE}) >= 1)""") { rewriterType: SMTEncoding =>
    val set = tla.filter(tla.name("x", IntT1), tla.emptySet(IntT1), tla.bool(false))
    val cardCmp = tla.constCard(tla.ge(tla.cardinality(set), tla.int(1)))
    val state = new SymbState(cardCmp, arena, Binding())
    // note that this optimization only works in the positive form. Its negation may be SAT.
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Cardinality({1, 2, 3} \ {2}) = 2""") { rewriterType: SMTEncoding =>
    def setminus(set: TBuilderInstruction, intVal: Int): TBuilderInstruction = {
      tla.filter(
          tla.name("t", IntT1),
          set,
          tla.not(tla.eql(tla.name("t", IntT1), tla.int(intVal))),
      )
    }

    val set = setminus(tla.enumSet(1.to(3).map(i => tla.int(i)): _*), 2)
    val cardinality = tla.cardinality(set)
    val eq = tla.eql(cardinality, tla.int(2))

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""IsFiniteSet({1, 2, 3}) = TRUE""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(1.to(3).map(i => tla.int(i)): _*)
    val isFiniteSet = tla.isFiniteSet(set)
    val state = new SymbState(isFiniteSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }
}
