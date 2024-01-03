package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp.TBuilderInstruction
import at.forsyte.apalache.tla.types.tla._

/**
 * Tests for assignments. The assignments were at the core of Apalache 0.5.x. In Apalache 0.6.x, they are preprocessed
 * into Skolemizable existential quantifiers. We keep the tests for regression.
 */
trait TestSymbStateRewriterAssignment extends RewriterBase {
  val ibI: TlaType1 = TupT1(IntT1, BoolT1, SetT1(IntT1))

  private val set12: TBuilderInstruction = enumSet(int(1), int(2))
  private val x_prime: TBuilderInstruction = prime(name("x", IntT1))
  private val x_primeS: TBuilderInstruction = prime(name("x", SetT1(IntT1)))
  private val x_primeFbi: TBuilderInstruction = prime(name("x", FunT1(BoolT1, IntT1)))
  private val x_primeFii: TBuilderInstruction = prime(name("x", FunT1(IntT1, IntT1)))
  private val x_primeFib: TBuilderInstruction = prime(name("x", FunT1(IntT1, BoolT1)))
  private val y_prime: TBuilderInstruction = prime(name("y", IntT1))
  private val boundName: TBuilderInstruction = name("t", IntT1)
  private val boundNameS: TBuilderInstruction = name("t", SetT1(IntT1))
  private val boundNameFbi: TBuilderInstruction = name("t", FunT1(BoolT1, IntT1))
  private val boundNameFii: TBuilderInstruction = name("t", FunT1(IntT1, IntT1))
  private val boundNameFib: TBuilderInstruction = name("t", FunT1(IntT1, BoolT1))
  private val boolset: TBuilderInstruction = enumSet(bool(false), bool(true))

  test("""\E t \in {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val asgn = skolem(exists(boundName, set12, assign(x_prime, boundName)))

    val state = new SymbState(asgn, arena, Binding())

    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // no contradiction introduced

    assertTlaExAndRestore(rewriter, nextState)
    assert(nextState.binding.toMap.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")
    rewriter.push()
    solverContext.assertGroundExpr(eql(boundCell.toBuilder, int(1)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(eql(boundCell.toBuilder, int(2)))
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(eql(boundCell.toBuilder, int(3)))
    assertUnsatOrExplain() // should not be possible
  }

  test("""assign in conjunction""") { rewriterType: SMTEncoding =>
    val and1 =
      and(
          assign(x_prime, int(1)),
          assign(y_prime, int(2)),
      )

    val state = new SymbState(and1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val x_cell = nextState.binding("x'").toBuilder
    val y_cell = nextState.binding("y'").toBuilder

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(eql(x_cell, int(1)))
    solverContext.assertGroundExpr(eql(y_cell, int(2)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(neql(x_cell, int(1)))
    assertUnsatOrExplain() // should not be possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(neql(y_cell, int(2)))
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in {}: x' = t ~~> FALSE""") { rewriterType: SMTEncoding =>
    val asgn = skolem(exists(boundName, emptySet(IntT1), assign(x_prime, boundName)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(name) =>
        assert(arena.cellFalse().toString == name)
        assert(nextState.binding.toMap.contains("x'"))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E t \in \in {t_2 \in {1}: FALSE}: x' \in {t} ~~> FALSE""") { rewriterType: SMTEncoding =>
    // a regression test
    def empty(set: TBuilderInstruction): TBuilderInstruction = {
      filter(name("t_2", IntT1), set, bool(false))
    }

    val asgn = skolem(exists(boundName, empty(enumSet(int(1))), assign(x_prime, boundName)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction should be introduced
    assert(solverContext.sat())
    // the assignment gives us false
    assertTlaExAndRestore(rewriter, nextState.setRex(not(unchecked(nextState.ex))))
  }

  test("""x' \in {1} /\ x' = 1 ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val asgn = assign(x_prime, int(1))
    val and1 = and(asgn, eql(x_prime, int(1)))

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
    solverContext.assertGroundExpr(not(unchecked(nextState.ex)))
    assert(!solverContext.sat())
  }

  test("""\E t \in {{1, 2}, {2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val set = enumSet(set12, enumSet(int(2), int(3)))
    val asgn = skolem(exists(boundNameS, set, assign(x_primeS, boundNameS)))

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
    val eq12 = eql(boundCell.toBuilder, set12)
    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2, 3}
    rewriter.push()
    val eq23 = eql(boundCell.toBuilder, enumSet(int(2), int(3)))
    val eqState23 = rewriter.rewriteUntilDone(nextState.setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = eql(boundCell.toBuilder, enumSet(int(1), int(3)))
    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in {{1, 2}, {1+1, 2, 3}} \ {{2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") {
    rewriterType: SMTEncoding =>
      // equal elements in different sets mess up picking from a set
      def setminus(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction = {
        // this is how Keramelizer translates setminus
        filter(name("t_2", SetT1(IntT1)), left, not(eql(name("t_2", SetT1(IntT1)), right)))

      }

      val set1to3 = enumSet(plus(int(1), int(1)), int(2), int(3))
      val set12 = enumSet(int(1), int(2))
      val twoSets = enumSet(set12, set1to3)
      val set23 = enumSet(int(2), int(3))
      val minus = setminus(twoSets, set23)
      val asgn =
        skolem(exists(boundNameS, minus, assign(x_primeS, boundNameS)))

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
      val eq12 = eql(boundCell.toBuilder, enumSet(int(1), int(2)))

      val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
      solverContext.assertGroundExpr(eqState12.ex)
      assert(solverContext.sat()) // ok
      rewriter.pop()
      // not equal to {1, 3}
      rewriter.push()
      val eq13 = eql(boundCell.toBuilder, enumSet(int(1), int(3)))

      val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
      solverContext.assertGroundExpr(eqState13.ex)
      assertUnsatOrExplain() // should not be possible
      rewriter.pop()
      // not equal to {2, 3}
      rewriter.push()
      val eq23 = eql(boundCell.toBuilder, enumSet(int(2), int(3)))

      val eqState23 = rewriter.rewriteUntilDone(nextState.setRex(eq23))
      solverContext.assertGroundExpr(eqState23.ex)
      assertUnsatOrExplain() // should not be possible
      rewriter.pop()
      // 2 is in the result
      rewriter.push()
      val in23 = in(int(2), boundCell.toBuilder)

      val inState23 = rewriter.rewriteUntilDone(nextState.setRex(in23))
      solverContext.assertGroundExpr(inState23.ex)
      assert(solverContext.sat()) // should be possible
      rewriter.pop()
  }

  test("""\E t \in SUBSET {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val set = powSet(set12)
    val asgn =
      skolem(exists(boundNameS, set, assign(x_primeS, boundNameS)))

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
    val eq12 = eql(boundCell.toBuilder, set12)

    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {1}
    rewriter.push()
    val eq1 = eql(boundCell.toBuilder, enumSet(int(1)))

    val eqState1 = rewriter.rewriteUntilDone(nextState.setRex(eq1))
    solverContext.assertGroundExpr(eqState1.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2}
    rewriter.push()
    val eq2 = eql(boundCell.toBuilder, enumSet(int(2)))

    val eqState2 = rewriter.rewriteUntilDone(nextState.setRex(eq2))
    solverContext.assertGroundExpr(eqState2.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {}, but this needs a type annotation
    rewriter.push()
    val eqEmpty = eql(boundCell.toBuilder, emptySet(IntT1))

    val eqStateEmpty = rewriter.rewriteUntilDone(nextState.setRex(eqEmpty))
    solverContext.assertGroundExpr(eqStateEmpty.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // not equal to {1, 2, 3}
    rewriter.push()
    val eq13 = eql(boundCell.toBuilder, enumSet(int(1), int(2), int(3)))

    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in {[x \in BOOLEAN |-> 0], [x2 \in BOOLEAN |-> 1]}: x' \in {t} ~~> TRUE""") {
    rewriterType: SMTEncoding =>
      val fun0 = funDef(int(0), name("x2", BoolT1) -> booleanSet())
      val fun1 = funDef(int(1), name("x3", BoolT1) -> booleanSet())
      val fun2 = funDef(int(2), name("x4", BoolT1) -> booleanSet())
      val set = enumSet(fun0, fun1)
      val asgn =
        skolem(exists(boundNameFbi, set, assign(x_primeFbi, boundNameFbi)))

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
      val eqFun0 = eql(boundCell.toBuilder, fun0)
      val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setRex(eqFun0))
      solverContext.assertGroundExpr(eqStateFun0.ex)
      assert(solverContext.sat()) // ok
      rewriter.pop()
      // may equal to fun1
      rewriter.push()
      val eqFun1 = eql(boundCell.toBuilder, fun1)
      val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setRex(eqFun1))
      solverContext.assertGroundExpr(eqStateFun1.ex)
      assert(solverContext.sat()) // also possible
      rewriter.pop()
      // not equal to fun2
      rewriter.push()
      val eqFun2 = eql(boundCell.toBuilder, fun2)
      val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setRex(eqFun2))
      solverContext.assertGroundExpr(eqStateFun2.ex)
      assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in [BOOLEAN -> {0, 1}]: x' \in {t} ~~> TRUE""") { rewriterType: SMTEncoding =>
    val fun0 = funDef(int(0), name("x", BoolT1) -> booleanSet())
    val fun1 = funDef(int(1), name("x", BoolT1) -> booleanSet())
    val fun2 = funDef(int(2), name("x", BoolT1) -> booleanSet())
    val set = funSet(booleanSet(), enumSet(int(0), int(1)))
    val asgn =
      skolem(exists(boundNameFbi, set, assign(x_primeFbi, boundNameFbi)))

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
    val eqFun0 = eql(boundCell.toBuilder, fun0)
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = eql(boundCell.toBuilder, fun1)
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = eql(boundCell.toBuilder, fun2)
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in [{} -> {0, 1}]: x' \in {t} ~~> FALSE""") { rewriterType: SMTEncoding =>
    // regression
    val set = funSet(emptySet(IntT1), enumSet(int(0), int(1)))
    val asgn =
      skolem(exists(boundNameFii, set, assign(x_primeFii, boundNameFii)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction introduced
    assert(solverContext.sat())
    // The assignment rule returns a function that is defined on the empty set.
    // It's probably similar to an empty set. In fact, the associated relation is empty.
    assertTlaExAndRestore(rewriter, nextState)
  }

  test("""\E t \in [0..(5 - 1) -> BOOLEAN]: x' \in {t} ~~> TRUE""") { rewriterType: SMTEncoding =>
    val domain = dotdot(int(0), minus(int(5), int(1)))
    val set = funSet(domain, boolset)
    val asgn =
      skolem(exists(boundNameFib, set, assign(x_primeFib, boundNameFib)))

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

  test("""\E t \in [0..4 -> Nat]: x' <- t""") { rewriterType: SMTEncoding =>
    val domain = dotdot(int(0), int(4))
    val set = funSet(domain, natSet())
    val asgn =
      skolem(exists(boundNameFii, set, assign(x_primeFii, boundNameFii)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    val x = nextState.binding("x'")
    val pred = ge(app(x.toBuilder, int(1)), int(0))

    assertTlaExAndRestore(rewriter, nextState.setRex(pred))
  }

  test("""\E t \in [0..4 -> Int]: x' <- t""") { rewriterType: SMTEncoding =>
    val domain = dotdot(int(0), int(4))
    val set = funSet(domain, intSet())
    val asgn =
      skolem(exists(boundNameFii, set, assign(x_primeFii, boundNameFii)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    // there is not much to check here, since it is just a function that returns an integer
  }

  // the model checker will never meet such an expression, as it will be optimized into several existentials by ExprOptimizer
  test("""\E t \in {<<1, FALSE, {1, 3}>>, <<2, TRUE, {4}>>}: x' = t""") { rewriterType: SMTEncoding =>
    val set1 = enumSet(int(1), int(3))
    val tuple1 = tuple(int(1), bool(false), set1)
    val set2 = enumSet(int(4))
    val tuple2 = tuple(int(2), bool(true), set2)
    val set = enumSet(tuple1, tuple2)
    val asgn =
      skolem(exists(name("t", ibI), set, assign(prime(name("x", ibI)), name("t", ibI))))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        assert(TupT1(IntT1, BoolT1, SetT1(IntT1)) == cell.cellType.toTlaType1)

        val membershipTest =
          and(
              in(app(prime(name("x", ibI)), int(1)), set12),
              in(app(prime(name("x", ibI)), int(2)), boolset),
              in(app(prime(name("x", ibI)), int(3)), enumSet(set1, set2)),
          )

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
