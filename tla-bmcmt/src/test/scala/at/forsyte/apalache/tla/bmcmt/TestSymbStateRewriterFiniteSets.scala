package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir.convenience.tla._
import at.forsyte.apalache.tla.lir.{BoolT1, IntT1, SetT1, TlaEx}
import at.forsyte.apalache.tla.pp.TlaInputError

trait TestSymbStateRewriterFiniteSets extends RewriterBase {
  private val intT = IntT1
  private val boolT = BoolT1
  private val intSetT = SetT1(IntT1)
  private val intSetSetT = SetT1(SetT1(IntT1))

  test("""Cardinality({1, 2, 3}) = 3""") { rewriterType: SMTEncoding =>
    val set = enumSet(1.to(3).map(int): _*)
    val cardinality = card(set.as(intSetT)).as(intT)
    val eq = eql(cardinality, int(3)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Cardinality(SUBSET {1, 2}) throws""") { rewriterType: SMTEncoding =>
    val set = enumSet(1.to(2).map(int): _*).as(intSetT)
    val powerset = powSet(set).as(intSetSetT)
    val cardinality = card(powerset).as(intT)

    val state = new SymbState(cardinality, arena, Binding())
    assertThrows[TlaInputError] {
      // this case should be handled by preprocessing
      create(rewriterType).rewriteUntilDone(state)
    }
  }

  test("""Cardinality({1, 2, 2, 2, 3, 3}) = 3""") { rewriterType: SMTEncoding =>
    val set = enumSet(Seq(1, 2, 2, 2, 3, 3).map(int): _*)
    val cardinality = card(set.as(intSetT)).as(intT)
    val eq = eql(cardinality, int(3)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 3}) >= 3)""") { rewriterType: SMTEncoding =>
    val set = enumSet(1.to(3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(3)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 3}) >= 4)""") { rewriterType: SMTEncoding =>
    val set = enumSet(1.to(3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(4)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 2, 3}) >= 4)""") { rewriterType: SMTEncoding =>
    val set = enumSet(Seq(1, 2, 2, 3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(4)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({1, 2, 2, 3, 3}) >= 4)""") { rewriterType: SMTEncoding =>
    val set = enumSet(Seq(1, 2, 2, 3, 3).map(int): _*)
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(4)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({}) >= 0)""") { rewriterType: SMTEncoding =>
    val set = enumSet()
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(0)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({}) >= 1)""") { rewriterType: SMTEncoding =>
    val set = enumSet()
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(1)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // note that this optimization only works in the positive form. Its negation may be SAT.
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({x \in {}: FALSE}) >= 0)""") { rewriterType: SMTEncoding =>
    val set = filter(name("x").as(intT), enumSet().as(intSetT), bool(false))
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(0)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    // note that this optimization only works in the positive form. Its negation may be SAT.
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
  }

  test("""Apalache!ConstCard(Cardinality({x \in {}: FALSE}) >= 1)""") { rewriterType: SMTEncoding =>
    val set = filter(name("x").as(intT), enumSet().as(intSetT), bool(false))
    val cardCmp = apalacheConstCard(ge(card(set.as(intSetT)).as(intT), int(1)).as(boolT)).as(boolT)
    val state = new SymbState(cardCmp, arena, Binding())
    // note that this optimization only works in the positive form. Its negation may be SAT.
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    assert(!solverContext.sat())
  }

  test("""Cardinality({1, 2, 3} \ {2}) = 2""") { rewriterType: SMTEncoding =>
    def setminus(set: TlaEx, intVal: Int): TlaEx = {
      filter(name("t").as(intT), set.as(intSetT), not(eql(name("t").as(intT), int(intVal)).as(boolT)).as(boolT)).as(
          intSetT)
    }

    val set = setminus(enumSet(1.to(3).map(int): _*).as(intSetT), 2)
    val cardinality = card(set.as(intSetT))
    val eq = eql(cardinality.as(intT), int(2)).as(boolT)

    val state = new SymbState(eq, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }

  test("""IsFiniteSet({1, 2, 3}) = TRUE""") { rewriterType: SMTEncoding =>
    val set = enumSet(1.to(3).map(int): _*)
    val isFiniteSet = isFin(set.as(intSetT)).as(boolT)
    val state = new SymbState(isFiniteSet, arena, Binding())
    assertTlaExAndRestore(create(rewriterType), state)
  }
}
