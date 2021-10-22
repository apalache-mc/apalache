package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.types._
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla._

/**
 * Tests for assignments. The assignments were at the core of Apalache 0.5.x. In Apalache 0.6.x, they are preprocessed
 * into Skolemizable existential quantifiers. We keep the tests for regression.
 */
trait TestSymbStateRewriterAssignment extends RewriterBase {
  private val types =
    Map("b" -> BoolT1(), "B" -> SetT1(BoolT1()), "i" -> IntT1(), "I" -> SetT1(IntT1()), "II" -> SetT1(SetT1(IntT1())),
        "b_to_i" -> FunT1(BoolT1(), IntT1()), "b_TO_i" -> SetT1(FunT1(BoolT1(), IntT1())),
        "i_to_b" -> FunT1(IntT1(), BoolT1()), "i_to_i" -> FunT1(IntT1(), IntT1()),
        "i_TO_i" -> SetT1(FunT1(IntT1(), IntT1())), "ibI" -> TupT1(IntT1(), BoolT1(), SetT1(IntT1())))
  private val set12: TlaEx = enumSet(int(1), int(2)).typed(SetT1(IntT1()))
  private val x_prime: TlaEx = prime(name("x") ? "i").typed(types, "i")
  private val y_prime: TlaEx = prime(name("y") ? "i").typed(types, "i")
  private val boundName: TlaEx = name("t").typed(IntT1())
  private val boolset: TlaEx = enumSet(bool(false), bool(true)).typed(SetT1(BoolT1()))

  test("""\E t \in {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: String =>
    val asgn = apalacheSkolem(exists(boundName, set12, assign(x_prime, boundName) ? "b") ? "b").typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())

    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // no contradiction introduced

    assertTlaExAndRestore(rewriter, nextState)
    assert(nextState.binding.toMap.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")
    rewriter.push()
    solverContext.assertGroundExpr(eql(boundCell.toNameEx ? "i", int(1)).typed(types, "b"))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(eql(boundCell.toNameEx ? "i", int(2)).typed(types, "b"))
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(eql(boundCell.toNameEx ? "i", int(3)).typed(types, "b"))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
  }

  test("""assign in conjunction""") { rewriterType: String =>
    val and1 =
      and(
          assign(x_prime, int(1)) ? "b",
          assign(y_prime, int(2)) ? "b"
      ).typed(types, "b")

    val state = new SymbState(and1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val x_cell = nextState.binding("x'").toNameEx
    val y_cell = nextState.binding("y'").toNameEx

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(eql(x_cell, int(1)).typed(types, "b"))
    solverContext.assertGroundExpr(eql(y_cell, int(2)).typed(types, "b"))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(neql(x_cell, int(1)).typed(types, "b"))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(neql(y_cell, int(2)).typed(types, "b"))
    assertUnsatOrExplain(rewriter, nextState) // should not be possible
  }

  test("""\E t \in {}: x' = t ~~> FALSE""") { rewriterType: String =>
    val asgn =
      apalacheSkolem(exists(boundName, enumSet() ? "I", assign(x_prime, boundName) ? "b") ? "b").typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(arena.cellFalse().toString == name)
        assert(nextState.binding.toMap.isEmpty)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E t \in \in {t_2 \in {1}: FALSE}: x' \in {t} ~~> FALSE""") { rewriterType: String =>
    // a regression test
    def empty(set: BuilderEx): TlaEx = {
      filter(name("t_2") ? "i", set ? "I", bool(false)).typed(types, "I")
    }

    val asgn =
      apalacheSkolem(exists(boundName, empty(enumSet(int(1))), assign(x_prime, boundName) ? "b") ? "b").typed(types,
          "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction should be introduced
    assert(solverContext.sat())
    // the assignment gives us false
    assertTlaExAndRestore(rewriter, nextState.setRex(not(nextState.ex).typed(BoolT1())))
  }

  test("""x' \in {1} /\ x' = 1 ~~> TRUE and [x -> $C$k]""") { rewriterType: String =>
    val asgn = assign(x_prime, int(1))
    val and1 = and(asgn ? "b", eql(x_prime, int(1)) ? "b").typed(types, "b")

    val state = new SymbState(and1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        assert(nextState.binding.toMap.size == 1)
        assert(nextState.binding.contains("x'"))
        nextState.binding("x'")

      case _ =>
        fail("Unexpected rewriting result")
    }

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(not(nextState.ex).typed(BoolT1()))
    assert(!solverContext.sat())
  }

  test("""\E t \in {{1, 2}, {2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: String =>
    val set = enumSet(set12, enumSet(int(2), int(3)) ? "I").typed(types, "II")
    val asgn = apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b").typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    // it returns true
    assertTlaExAndRestore(rewriter, nextState)

    assert(nextState.binding.toMap.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")

    // may equal to {1, 2}
    rewriter.push()
    val eq12 = eql(boundCell.toNameEx ? "I", set12).typed(types, "b")
    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2, 3}
    rewriter.push()
    val eq23 = eql(boundCell.toNameEx ? "I", enumSet(int(2), int(3)) ? "I").typed(types, "b")
    val eqState23 = rewriter.rewriteUntilDone(nextState.setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = eql(boundCell.toNameEx ? "I", enumSet(int(1), int(3)) ? "I").typed(types, "b")
    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
  }

  test("""\E t \in {{1, 2}, {1+1, 2, 3}} \ {{2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: String =>
    // equal elements in different sets mess up picking from a set
    def setminus(left: TlaEx, right: TlaEx): TlaEx = {
      // this is how Keramelizer translates setminus
      filter(name("t_2") ? "I", left ? "II", not(eql(name("t_2") ? "I", right ? "I") ? "b") ? "b")
        .typed(types, "II")
    }

    val set1to3 = enumSet(plus(int(1), int(1)) ? "i", int(2), int(3)).typed(types, "I")
    val set12 = enumSet(int(1), int(2)).typed(types, "I")
    val twoSets = enumSet(set12, set1to3).typed(types, "II")
    val set23 = enumSet(int(2), int(3)).typed(types, "I")
    val minus = setminus(twoSets, set23)
    val asgn =
      apalacheSkolem(exists(boundName, minus, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)

    assert(nextState.binding.toMap.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")

    // may equal to {1, 2}
    rewriter.push()
    val eq12 = eql(boundCell.toNameEx ? "I", enumSet(int(1), int(2)) ? "I")
      .typed(types, "b")
    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = eql(boundCell.toNameEx ? "I", enumSet(int(1), int(3)) ? "I")
      .typed(types, "b")
    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
    rewriter.pop()
    // not equal to {2, 3}
    rewriter.push()
    val eq23 = eql(boundCell.toNameEx ? "I", enumSet(int(2), int(3)) ? "I")
      .typed(types, "b")
    val eqState23 = rewriter.rewriteUntilDone(nextState.setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assertUnsatOrExplain(rewriter, eqState23) // should not be possible
    rewriter.pop()
    // 2 is in the result
    rewriter.push()
    val in23 = in(int(2), boundCell.toNameEx ? "I")
      .typed(types, "b")
    val inState23 = rewriter.rewriteUntilDone(nextState.setRex(in23))
    solverContext.assertGroundExpr(inState23.ex)
    assert(solverContext.sat()) // should be possible
    rewriter.pop()
  }

  test("""\E t \in SUBSET {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: String =>
    val set = powSet(set12).typed(types, "II")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.toMap.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to {1, 2}
    rewriter.push()
    val eq12 = eql(boundCell.toNameEx ? "I", set12)
      .typed(types, "b")
    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {1}
    rewriter.push()
    val eq1 = eql(boundCell.toNameEx ? "I", enumSet(int(1)) ? "I")
      .typed(types, "b")
    val eqState1 = rewriter.rewriteUntilDone(nextState.setRex(eq1))
    solverContext.assertGroundExpr(eqState1.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2}
    rewriter.push()
    val eq2 = eql(boundCell.toNameEx ? "I", enumSet(int(2)) ? "I")
      .typed(types, "b")
    val eqState2 = rewriter.rewriteUntilDone(nextState.setRex(eq2))
    solverContext.assertGroundExpr(eqState2.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {}, but this needs a type annotation
    rewriter.push()
    val eqEmpty = eql(boundCell.toNameEx ? "I", enumSet() ? "I")
      .typed(types, "b")
    val eqStateEmpty = rewriter.rewriteUntilDone(nextState.setRex(eqEmpty))
    solverContext.assertGroundExpr(eqStateEmpty.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // not equal to {1, 2, 3}
    rewriter.push()
    val eq13 = eql(boundCell.toNameEx ? "I", enumSet(int(1), int(2), int(3)) ? "I")
      .typed(types, "b")
    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain(rewriter, eqState13) // should not be possible
  }

  test("""\E t \in {[x \in BOOLEAN |-> 0], [x2 \in BOOLEAN |-> 1]}: x' \in {t} ~~> TRUE""") { rewriterType: String =>
    val fun0 = funDef(int(0), name("x2") ? "b", booleanSet() ? "B").typed(types, "b_to_i")
    val fun1 = funDef(int(1), name("x3") ? "b", booleanSet() ? "B").typed(types, "b_to_i")
    val fun2 = funDef(int(2), name("x4") ? "b", booleanSet() ? "B").typed(types, "b_to_i")
    val set = enumSet(fun0, fun1).typed(types, "b_TO_i")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    assertTlaExAndRestore(rewriter, nextState)
    assert(nextState.binding.toMap.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")

    // may equal to fun0
    rewriter.push()
    val eqFun0 = eql(boundCell.toNameEx ? "b_to_i", fun0).typed(types, "b")
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = eql(boundCell.toNameEx ? "b_to_i", fun1).typed(types, "b")
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = eql(boundCell.toNameEx ? "b_to_i", fun2).typed(types, "b")
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain(rewriter, eqStateFun2) // should not be possible
  }

  test("""\E t \in [BOOLEAN -> {0, 1}]: x' \in {t} ~~> TRUE""") { rewriterType: String =>
    val fun0 = funDef(int(0), name("x") ? "b", booleanSet() ? "B").typed(types, "b_to_i")
    val fun1 = funDef(int(1), name("x") ? "b", booleanSet() ? "B").typed(types, "b_to_i")
    val fun2 = funDef(int(2), name("x") ? "b", booleanSet() ? "B").typed(types, "b_to_i")
    val set = funSet(booleanSet() ? "I", enumSet(int(0), int(1)) ? "I").typed(types, "b_TO_i")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b").typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val boundCell =
      nextState.ex match {
        case NameEx(name) =>
          assert(arena.cellTrue().toString == name)
          assert(nextState.binding.toMap.size == 1)
          assert(nextState.binding.contains("x'"))
          nextState.binding("x'")

        case _ =>
          fail("Unexpected rewriting result")
      }

    // no contradiction introduced
    assert(solverContext.sat())
    // may equal to fun0
    rewriter.push()
    val eqFun0 = eql(boundCell.toNameEx ? "b_to_i", fun0).typed(types, "b")
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = eql(boundCell.toNameEx ? "b_to_i", fun1).typed(types, "b")
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = eql(boundCell.toNameEx ? "b_to_i", fun2).typed(types, "b")
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain(rewriter, eqStateFun2) // should not be possible
  }

  test("""\E t \in [{} -> {0, 1}]: x' \in {t} ~~> FALSE""") { rewriterType: String =>
    // regression
    val set = funSet(enumSet() ? "I", enumSet(int(0), int(1)) ? "I").typed(types, "i_TO_i")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    // The assignment rule returns a function that is defined on the empty set.
    // It's probably similar to an empty set. In fact, the associated relation is empty.
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""\E t \in [0..(5 - 1) -> BOOLEAN]: x' \in {t} ~~> TRUE""") { rewriterType: String =>
    val domain = dotdot(int(0), minus(int(5), int(1)) ? "i").typed(types, "I")
    val set = funSet(domain, boolset).typed(types, "i_to_b")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(arena.cellTrue().toString == name)
        assert(nextState.binding.toMap.size == 1)
        assert(nextState.binding.contains("x'"))
        nextState.binding("x'")

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E t \in [0..4 -> Nat]: x' <- t""") { rewriterType: String =>
    val domain = dotdot(int(0), int(4)).typed(types, "I")
    val set = funSet(domain, natSet() ? "I").typed(types, "i_TO_i")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    val x = nextState.binding("x'")
    val pred = ge(appFun(x.toNameEx ? "i_to_i", int(1)) ? "i", int(0))
      .typed(types, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(pred))
  }

  test("""\E t \in [0..4 -> Int]: x' <- t""") { rewriterType: String =>
    val domain = dotdot(int(0), int(4)).typed(types, "I")
    val set = funSet(domain, intSet() ? "I").typed(types, "i_TO_i")
    val asgn =
      apalacheSkolem(exists(boundName, set, assign(x_prime, boundName) ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
  // there is not much to check here, since it is just a function that returns an integer
  }

  // the model checker will never meet such an expression, as it will be optimized into several existentials by ExprOptimizer
  test("""\E t \in {<<1, FALSE, {1, 3}>>, <<2, TRUE, {4}>>}: x' = t""") { rewriterType: String =>
    val set1 = enumSet(int(1), int(3)).typed(types, "I")
    val tuple1 = tuple(int(1), bool(false), set1).typed(types, "ibI")
    val set2 = enumSet(int(4)).typed(types, "I")
    val tuple2 = tuple(int(2), bool(true), set2).typed(types, "ibI")
    val set = enumSet(tuple1, tuple2).typed(SetT1(types("ibI")))
    val asgn =
      apalacheSkolem(exists(name("t") ? "ibI", set,
              assign(prime(name("x") ? "ibI") ? "ibI", name("t") ? "ibI") ? "b") ? "b")
        .typed(types, "b")

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        assert(TupleT(List(IntT(), BoolT(), FinSetT(IntT()))) == cell.cellType)

        val membershipTest =
          and(in(appFun(prime(name("x") ? "ibI") ? "ibI", int(1)) ? "i", set12) ? "b",
              in(appFun(prime(name("x") ? "ibI") ? "ibI", int(2)) ? "i", boolset) ? "b",
              in(appFun(prime(name("x") ? "ibI") ? "ibI", int(3)) ? "i", enumSet(set1, set2) ? "II") ? "b")
            .typed(types, "b")

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
