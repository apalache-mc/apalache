package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

/**
 * Tests for assignments. The assignments were at the core of Apalache 0.5.x. In Apalache 0.6.x, they are preprocessed
 * into Skolemizable existential quantifiers. We keep the tests for regression.
 */
trait TestSymbStateRewriterAssignment extends RewriterBase {
  val ibI: TlaType1 = TupT1(IntT1, BoolT1, SetT1(IntT1))

  private val set12: TBuilderInstruction = tla.enumSet(tla.int(1), tla.int(2))
  private val x_prime: TBuilderInstruction = tla.prime(tla.name("x", IntT1))
  private val x_primeS: TBuilderInstruction = tla.prime(tla.name("x", SetT1(IntT1)))
  private val x_primeFbi: TBuilderInstruction = tla.prime(tla.name("x", FunT1(BoolT1, IntT1)))
  private val x_primeFii: TBuilderInstruction = tla.prime(tla.name("x", FunT1(IntT1, IntT1)))
  private val x_primeFib: TBuilderInstruction = tla.prime(tla.name("x", FunT1(IntT1, BoolT1)))
  private val y_prime: TBuilderInstruction = tla.prime(tla.name("y", IntT1))
  private val boundName: TBuilderInstruction = tla.name("t", IntT1)
  private val boundNameS: TBuilderInstruction = tla.name("t", SetT1(IntT1))
  private val boundNameFbi: TBuilderInstruction = tla.name("t", FunT1(BoolT1, IntT1))
  private val boundNameFii: TBuilderInstruction = tla.name("t", FunT1(IntT1, IntT1))
  private val boundNameFib: TBuilderInstruction = tla.name("t", FunT1(IntT1, BoolT1))
  private val boolset: TBuilderInstruction = tla.enumSet(tla.bool(false), tla.bool(true))

  test("""\E t \in {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val asgn = tla.skolem(tla.exists(boundName, set12, tla.assign(x_prime, boundName)))

    val state = new SymbState(asgn, arena, Binding())

    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // no contradiction introduced

    assertTlaExAndRestore(rewriter, nextState)
    assert(nextState.binding.toMap.size == 1)
    assert(nextState.binding.contains("x'"))
    val boundCell = nextState.binding("x'")
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(cellEx(boundCell), tla.int(1)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(cellEx(boundCell), tla.int(2)))
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(cellEx(boundCell), tla.int(3)))
    assertUnsatOrExplain() // should not be possible
  }

  test("""assign in conjunction""") { rewriterType: SMTEncoding =>
    val and1 =
      tla.and(
          tla.assign(x_prime, tla.int(1)),
          tla.assign(y_prime, tla.int(2)),
      )

    val state = new SymbState(and1, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val x_cell = cellEx(nextState.binding("x'"))
    val y_cell = cellEx(nextState.binding("y'"))

    assert(solverContext.sat()) // no contradiction introduced
    rewriter.push()
    solverContext.assertGroundExpr(tla.eql(x_cell, tla.int(1)))
    solverContext.assertGroundExpr(tla.eql(y_cell, tla.int(2)))
    assert(solverContext.sat()) // ok
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.neql(x_cell, tla.int(1)))
    assertUnsatOrExplain() // should not be possible
    rewriter.pop()
    rewriter.push()
    solverContext.assertGroundExpr(tla.neql(y_cell, tla.int(2)))
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in {}: x' = t ~~> FALSE""") { rewriterType: SMTEncoding =>
    val asgn = tla.skolem(tla.exists(boundName, tla.emptySet(IntT1), tla.assign(x_prime, boundName)))

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
      tla.filter(tla.name("t_2", IntT1), set, tla.bool(false))
    }

    val asgn = tla.skolem(tla.exists(boundName, empty(tla.enumSet(tla.int(1))), tla.assign(x_prime, boundName)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    // no contradiction should be introduced
    assert(solverContext.sat())
    // the assignment gives us false
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(tla.unchecked(nextState.ex))))
  }

  test("""x' \in {1} /\ x' = 1 ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val asgn = tla.assign(x_prime, tla.int(1))
    val and1 = tla.and(asgn, tla.eql(x_prime, tla.int(1)))

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
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assert(!solverContext.sat())
  }

  test("""\E t \in {{1, 2}, {2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val set = tla.enumSet(set12, tla.enumSet(tla.int(2), tla.int(3)))
    val asgn = tla.skolem(tla.exists(boundNameS, set, tla.assign(x_primeS, boundNameS)))

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
    val eq12 = tla.eql(cellEx(boundCell), set12)
    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2, 3}
    rewriter.push()
    val eq23 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(2), tla.int(3)))
    val eqState23 = rewriter.rewriteUntilDone(nextState.setRex(eq23))
    solverContext.assertGroundExpr(eqState23.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to {1, 3}
    rewriter.push()
    val eq13 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(1), tla.int(3)))
    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in {{1, 2}, {1+1, 2, 3}} \ {{2, 3}}: x' \in {t} ~~> TRUE and [x -> $C$k]""") {
    rewriterType: SMTEncoding =>
      // equal elements in different sets mess up picking from a set
      def setminus(left: TBuilderInstruction, right: TBuilderInstruction): TBuilderInstruction = {
        // this is how Keramelizer translates setminus
        tla.filter(tla.name("t_2", SetT1(IntT1)), left, tla.not(tla.eql(tla.name("t_2", SetT1(IntT1)), right)))

      }

      val set1to3 = tla.enumSet(tla.plus(tla.int(1), tla.int(1)), tla.int(2), tla.int(3))
      val set12 = tla.enumSet(tla.int(1), tla.int(2))
      val twoSets = tla.enumSet(set12, set1to3)
      val set23 = tla.enumSet(tla.int(2), tla.int(3))
      val minus = setminus(twoSets, set23)
      val asgn =
        tla.skolem(tla.exists(boundNameS, minus, tla.assign(x_primeS, boundNameS)))

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
      val eq12 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(1), tla.int(2)))

      val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
      solverContext.assertGroundExpr(eqState12.ex)
      assert(solverContext.sat()) // ok
      rewriter.pop()
      // not equal to {1, 3}
      rewriter.push()
      val eq13 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(1), tla.int(3)))

      val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
      solverContext.assertGroundExpr(eqState13.ex)
      assertUnsatOrExplain() // should not be possible
      rewriter.pop()
      // not equal to {2, 3}
      rewriter.push()
      val eq23 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(2), tla.int(3)))

      val eqState23 = rewriter.rewriteUntilDone(nextState.setRex(eq23))
      solverContext.assertGroundExpr(eqState23.ex)
      assertUnsatOrExplain() // should not be possible
      rewriter.pop()
      // 2 is in the result
      rewriter.push()
      val in23 = tla.in(tla.int(2), cellEx(boundCell))

      val inState23 = rewriter.rewriteUntilDone(nextState.setRex(in23))
      solverContext.assertGroundExpr(inState23.ex)
      assert(solverContext.sat()) // should be possible
      rewriter.pop()
  }

  test("""\E t \in SUBSET {1, 2}: x' \in {t} ~~> TRUE and [x -> $C$k]""") { rewriterType: SMTEncoding =>
    val set = tla.powSet(set12)
    val asgn =
      tla.skolem(tla.exists(boundNameS, set, tla.assign(x_primeS, boundNameS)))

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
    val eq12 = tla.eql(cellEx(boundCell), set12)

    val eqState12 = rewriter.rewriteUntilDone(nextState.setRex(eq12))
    solverContext.assertGroundExpr(eqState12.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {1}
    rewriter.push()
    val eq1 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(1)))

    val eqState1 = rewriter.rewriteUntilDone(nextState.setRex(eq1))
    solverContext.assertGroundExpr(eqState1.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {2}
    rewriter.push()
    val eq2 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(2)))

    val eqState2 = rewriter.rewriteUntilDone(nextState.setRex(eq2))
    solverContext.assertGroundExpr(eqState2.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to {}, but this needs a type annotation
    rewriter.push()
    val eqEmpty = tla.eql(cellEx(boundCell), tla.emptySet(IntT1))

    val eqStateEmpty = rewriter.rewriteUntilDone(nextState.setRex(eqEmpty))
    solverContext.assertGroundExpr(eqStateEmpty.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // not equal to {1, 2, 3}
    rewriter.push()
    val eq13 = tla.eql(cellEx(boundCell), tla.enumSet(tla.int(1), tla.int(2), tla.int(3)))

    val eqState13 = rewriter.rewriteUntilDone(nextState.setRex(eq13))
    solverContext.assertGroundExpr(eqState13.ex)
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in {[x \in BOOLEAN |-> 0], [x2 \in BOOLEAN |-> 1]}: x' \in {t} ~~> TRUE""") {
    rewriterType: SMTEncoding =>
      val fun0 = tla.funDef(tla.int(0), tla.name("x2", BoolT1) -> tla.booleanSet())
      val fun1 = tla.funDef(tla.int(1), tla.name("x3", BoolT1) -> tla.booleanSet())
      val fun2 = tla.funDef(tla.int(2), tla.name("x4", BoolT1) -> tla.booleanSet())
      val set = tla.enumSet(fun0, fun1)
      val asgn =
        tla.skolem(tla.exists(boundNameFbi, set, tla.assign(x_primeFbi, boundNameFbi)))

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
      val eqFun0 = tla.eql(cellEx(boundCell), fun0)
      val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setRex(eqFun0))
      solverContext.assertGroundExpr(eqStateFun0.ex)
      assert(solverContext.sat()) // ok
      rewriter.pop()
      // may equal to fun1
      rewriter.push()
      val eqFun1 = tla.eql(cellEx(boundCell), fun1)
      val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setRex(eqFun1))
      solverContext.assertGroundExpr(eqStateFun1.ex)
      assert(solverContext.sat()) // also possible
      rewriter.pop()
      // not equal to fun2
      rewriter.push()
      val eqFun2 = tla.eql(cellEx(boundCell), fun2)
      val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setRex(eqFun2))
      solverContext.assertGroundExpr(eqStateFun2.ex)
      assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in [BOOLEAN -> {0, 1}]: x' \in {t} ~~> TRUE""") { rewriterType: SMTEncoding =>
    val fun0 = tla.funDef(tla.int(0), tla.name("x", BoolT1) -> tla.booleanSet())
    val fun1 = tla.funDef(tla.int(1), tla.name("x", BoolT1) -> tla.booleanSet())
    val fun2 = tla.funDef(tla.int(2), tla.name("x", BoolT1) -> tla.booleanSet())
    val set = tla.funSet(tla.booleanSet(), tla.enumSet(tla.int(0), tla.int(1)))
    val asgn =
      tla.skolem(tla.exists(boundNameFbi, set, tla.assign(x_primeFbi, boundNameFbi)))

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
    val eqFun0 = tla.eql(cellEx(boundCell), fun0)
    val eqStateFun0 = rewriter.rewriteUntilDone(nextState.setRex(eqFun0))
    solverContext.assertGroundExpr(eqStateFun0.ex)
    assert(solverContext.sat()) // ok
    rewriter.pop()
    // may equal to fun1
    rewriter.push()
    val eqFun1 = tla.eql(cellEx(boundCell), fun1)
    val eqStateFun1 = rewriter.rewriteUntilDone(nextState.setRex(eqFun1))
    solverContext.assertGroundExpr(eqStateFun1.ex)
    assert(solverContext.sat()) // also possible
    rewriter.pop()
    // not equal to fun2
    rewriter.push()
    val eqFun2 = tla.eql(cellEx(boundCell), fun2)
    val eqStateFun2 = rewriter.rewriteUntilDone(nextState.setRex(eqFun2))
    solverContext.assertGroundExpr(eqStateFun2.ex)
    assertUnsatOrExplain() // should not be possible
  }

  test("""\E t \in [{} -> {0, 1}]: x' \in {t} ~~> FALSE""") { rewriterType: SMTEncoding =>
    // regression
    val set = tla.funSet(tla.emptySet(IntT1), tla.enumSet(tla.int(0), tla.int(1)))
    val asgn =
      tla.skolem(tla.exists(boundNameFii, set, tla.assign(x_primeFii, boundNameFii)))

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
    val domain = tla.dotdot(tla.int(0), tla.minus(tla.int(5), tla.int(1)))
    val set = tla.funSet(domain, boolset)
    val asgn =
      tla.skolem(tla.exists(boundNameFib, set, tla.assign(x_primeFib, boundNameFib)))

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
    val domain = tla.dotdot(tla.int(0), tla.int(4))
    val set = tla.funSet(domain, tla.natSet())
    val asgn =
      tla.skolem(tla.exists(boundNameFii, set, tla.assign(x_primeFii, boundNameFii)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    val x = nextState.binding("x'")
    val pred = tla.ge(tla.app(cellEx(x), tla.int(1)), tla.int(0))

    assertTlaExAndRestore(rewriter, nextState.setRex(pred))
  }

  test("""\E t \in [0..4 -> Int]: x' <- t""") { rewriterType: SMTEncoding =>
    val domain = tla.dotdot(tla.int(0), tla.int(4))
    val set = tla.funSet(domain, tla.intSet())
    val asgn =
      tla.skolem(tla.exists(boundNameFii, set, tla.assign(x_primeFii, boundNameFii)))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteUntilDone(state)
    assert(rewriter.solverContext.sat())
    // there is not much to check here, since it is just a function that returns an integer
  }

  // the model checker will never meet such an expression, as it will be optimized into several existentials by ExprOptimizer
  test("""\E t \in {<<1, FALSE, {1, 3}>>, <<2, TRUE, {4}>>}: x' = t""") { rewriterType: SMTEncoding =>
    val set1 = tla.enumSet(tla.int(1), tla.int(3))
    val tuple1 = tla.tuple(tla.int(1), tla.bool(false), set1)
    val set2 = tla.enumSet(tla.int(4))
    val tuple2 = tla.tuple(tla.int(2), tla.bool(true), set2)
    val set = tla.enumSet(tuple1, tuple2)
    val asgn =
      tla.skolem(tla.exists(tla.name("t", ibI), set, tla.assign(tla.prime(tla.name("x", ibI)), tla.name("t", ibI))))

    val state = new SymbState(asgn, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case NameEx(_) =>
        val cell = nextState.binding("x'")
        assert(TupT1(IntT1, BoolT1, SetT1(IntT1)) == cell.cellType.toTlaType1)

        val membershipTest =
          tla.and(
              tla.in(tla.app(tla.prime(tla.name("x", ibI)), tla.int(1)), set12),
              tla.in(tla.app(tla.prime(tla.name("x", ibI)), tla.int(2)), boolset),
              tla.in(tla.app(tla.prime(tla.name("x", ibI)), tla.int(3)), tla.enumSet(set1, set2)),
          )

        assertTlaExAndRestore(rewriter, nextState.setRex(membershipTest))

      case _ =>
        fail("Unexpected rewriting result")
    }
  }
}
