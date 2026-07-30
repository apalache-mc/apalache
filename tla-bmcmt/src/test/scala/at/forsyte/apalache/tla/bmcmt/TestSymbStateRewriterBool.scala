package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.infra.passes.options.SMTEncoding
import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.NoRule
import at.forsyte.apalache.tla.bmcmt.types.CellTFrom
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.typecomp._
import at.forsyte.apalache.tla.types.tla

trait TestSymbStateRewriterBool extends RewriterBase {
  // these are handy variables that will be overwritten by before
  private var x: ArenaCell = new ArenaCell(100000, CellTFrom(IntT1))
  private var y: ArenaCell = new ArenaCell(100001, CellTFrom(IntT1))
  private var set: ArenaCell = new ArenaCell(100001, CellTFrom(SetT1(IntT1)))
  private var xyBinding = Binding()

  def prepareArena(): Unit = {
    arena = arena.appendCell(BoolT1) // we have to give bindings to the type finder
    x = arena.topCell
    arena = arena.appendCell(BoolT1) // we have to give bindings to the type finder
    y = arena.topCell
    arena = arena.appendCell(SetT1(IntT1))
    set = arena.topCell
    xyBinding = Binding("x" -> x, "y" -> y, "S" -> set)
  }

  test("FALSE ~~> $C$0") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.bool(false)
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$0")(Untyped)
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("TRUE ~~> $C$1") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.bool(true)
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$1")(Untyped)
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("BOOLEAN ~~> c_BOOLEAN") { rewriterType: SMTEncoding =>
    prepareArena()
    val boolset = tla.booleanSet()
    val state = new SymbState(boolset, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$2")(Untyped)
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("x => y ~~> ~x \\/ y") { rewriterType: SMTEncoding =>
    // outside of KerA+, should be handled by Keramelizer and Normalizer
    prepareArena()
    val ex = tla.impl(boolName("x"), boolName("y"))
    val state = new SymbState(ex, arena, xyBinding)
    assert(NoRule() == create(rewriterType).rewriteOnce(state))
  }

  test("x <=> y") { rewriterType: SMTEncoding =>
    // outside of KerA+, should be handled by Keramelizer and Normalizer
    arena = arena.appendCell(BoolT1)
    val left = arena.topCell
    arena = arena.appendCell(BoolT1)
    val right = arena.topCell
    val ex = tla.equiv(cellEx(left), cellEx(right))
    val state = new SymbState(ex, arena, xyBinding)
    assert(NoRule() == create(rewriterType).rewriteOnce(state))
  }

  test("""IF-THEN-ELSE with \E: IF \E i \in {}: x' \in {i} THEN x' ELSE 0""") { rewriterType: SMTEncoding =>
    // this tricky test comes from Bakery, where an assignment is made in one branch of a conjunction
    prepareArena()
    val exists =
      tla.skolem(
          tla.exists(intName("i"), tla.emptySet(IntT1), tla.in(tla.prime(intName("x")), tla.enumSet(intName("i"))))
      )
    val ite = tla.ite(exists, tla.prime(intName("x")), tla.int(0))

    val state = new SymbState(ite, arena, Binding())
    val rewriter = createWithoutCache(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val eq = tla.eql(tla.int(0), tla.unchecked(nextState.ex))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""~c_i ~~> b_new""") { rewriterType: SMTEncoding =>
    prepareArena()
    arena = arena.appendCell(BoolT1)
    val cell = arena.topCell

    val ex = tla.not(cellEx(cell))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(_) =>
            val eq = tla.eql(cellEx(cell), cellEx(arena.cellFalse()))
            solverContext.assertGroundExpr(eq)
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~x ~~> TRUE""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.not(boolName("x"))
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(tla.unchecked(nextState.ex), tla.bool(true))))
  }

  test("""FALSE = TRUE ~~> FALSE""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.eql(cellEx(arena.cellFalse()), cellEx(arena.cellTrue()))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla.eql(tla.unchecked(nextState.ex), cellEx(arena.cellFalse()))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""x = TRUE ~~> FALSE when x = FALSE""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.eql(boolName("x"), tla.bool(true))
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla.eql(tla.unchecked(nextState.ex), tla.bool(false))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""~(x = TRUE) ~~> TRUE when x = FALSE""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.not(tla.eql(boolName("x"), tla.bool(true)))
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla.eql(tla.unchecked(nextState.ex), tla.bool(true))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""FALSE /\ TRUE ~~> $B$0""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.and(tla.bool(false), tla.bool(true))
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(state.arena.cellFalse().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_1 /\ c_2 ~~> b_new""") { rewriterType: SMTEncoding =>
    prepareArena()
    arena = arena.appendCell(BoolT1)
    val c1 = arena.topCell
    arena = arena.appendCell(BoolT1)
    val c2 = arena.topCell

    val ex = tla.and(cellEx(c1), cellEx(c2))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(_) =>
            assert(solverContext.sat())
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            val eq1 = tla.eql(cellEx(c1), cellEx(arena.cellFalse()))
            solverContext.assertGroundExpr(eq1)
            assert(!solverContext.sat())
            rewriter.pop()
            val eq2 = tla.eql(cellEx(c1), cellEx(arena.cellTrue()))
            solverContext.assertGroundExpr(eq2)
            assert(solverContext.sat())
            val eq3 = tla.eql(cellEx(c2), cellEx(arena.cellTrue()))
            solverContext.assertGroundExpr(eq3)
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""empty \/ ~~> $B$0""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.or()
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellFalse().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""empty /\ ~~> $B$1""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.and()
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellTrue().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""FALSE \/ TRUE ~~> $B$1""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.or(tla.bool(false), tla.bool(true))
    val state = new SymbState(ex, arena, Binding())
    create(rewriterType).rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellTrue().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_1 \/ c_2 ~~> b_new""") { rewriterType: SMTEncoding =>
    prepareArena()
    arena = arena.appendCell(BoolT1)
    val left = arena.topCell
    arena = arena.appendCell(BoolT1)
    val right = arena.topCell

    val ex = tla.or(cellEx(left), cellEx(right))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(_) =>
            val eq1 = tla.eql(cellEx(left), cellEx(arena.cellFalse()))
            solverContext.assertGroundExpr(eq1)
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            val eq2 = tla.eql(cellEx(right), cellEx(arena.cellFalse()))
            solverContext.assertGroundExpr(eq2)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~($B$1 = $B$2) ~~> $B$3""") { rewriterType: SMTEncoding =>
    prepareArena()
    arena = arena.appendCell(BoolT1)
    val left = arena.topCell
    arena = arena.appendCell(BoolT1)
    val right = arena.topCell

    val ex = tla.not(tla.eql(cellEx(left), cellEx(right)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(_) =>
        solverContext.assertGroundExpr(predEx)
        rewriter.push()
        // both false
        assert(solverContext.sat())
        val eq1 = tla.eql(cellEx(left), cellEx(arena.cellFalse()))
        solverContext.assertGroundExpr(eq1)
        assert(solverContext.sat())
        rewriter.push()
        val eq2 = tla.eql(cellEx(right), cellEx(arena.cellFalse()))
        solverContext.assertGroundExpr(eq2)
        assert(!solverContext.sat())
        rewriter.pop()
        val eq3 = tla.eql(cellEx(right), cellEx(arena.cellTrue()))
        solverContext.assertGroundExpr(eq3)
        assert(solverContext.sat())
        rewriter.pop()
        // both true
        val eq4 = tla.eql(cellEx(left), cellEx(arena.cellTrue()))
        solverContext.assertGroundExpr(eq4)
        assert(solverContext.sat())
        rewriter.push()
        val eq5 = tla.eql(cellEx(right), cellEx(arena.cellTrue()))
        solverContext.assertGroundExpr(eq5)
        assert(!solverContext.sat())
        rewriter.pop()
        val eq6 = tla.eql(cellEx(right), cellEx(arena.cellFalse()))
        solverContext.assertGroundExpr(eq6)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E x \in {}: TRUE ~~> FALSE""") { rewriterType: SMTEncoding =>
    prepareArena()
    val ex = tla.exists(intName("x"), tla.emptySet(IntT1), tla.bool(true))
    val state = new SymbState(ex, arena, Binding())
    val nextState = create(rewriterType).rewriteUntilDone(state)
    assert(arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""\E x \in {1, 2, 3}: x = 2 ~~> $B$k""") { rewriterType: SMTEncoding =>
    prepareArena()
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.exists(intName("x"), set123, tla.eql(tla.int(2), intName("x")))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assertUnsatOrExplain()
  }

  /** Jure, 9.12.19: Why should this throw? */
  test("""\E x \in {1, 2}: y' := x ~~> 2 assignments, regression""") { rewriterType: SMTEncoding =>
    prepareArena()
    val set12 = tla.enumSet(tla.int(1), tla.int(2))
    // an assignment inside an existential quantifier is tricky, as we can multiple values to variables
    val ex = tla.exists(
        intName("x"),
        set12,
        tla.assign(tla.prime(intName("y")), intName("x")),
    )
    ////
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    assertThrows[NotImplementedError] {
      // TODO: implement multiple assignments in expanded quantifiers
      val nextState = rewriter.rewriteUntilDone(state)
      assert(solverContext.sat())
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      assert(solverContext.sat())
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
      assertUnsatOrExplain()
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      val eq1 = tla.eql(tla.int(1), cellEx(nextState.binding("y'")))
      solverContext.assertGroundExpr(eq1)
      assert(solverContext.sat())
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      val eq2 = tla.eql(tla.int(2), cellEx(nextState.binding("y'")))
      solverContext.assertGroundExpr(eq2)
      assert(solverContext.sat())
      rewriter.pop()
    }
  }

  test("""\E x \in {1, 2, 3}: x > 4 ~~> $B$k""") { rewriterType: SMTEncoding =>
    prepareArena()
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.exists(intName("x"), set123, tla.gt(intName("x"), tla.int(4)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain()
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assert(solverContext.sat())
  }

  test("""\E x \in {t \in {1}: FALSE}: x > 4, regression""") { rewriterType: SMTEncoding =>
    prepareArena()
    def dynEmpty(left: TBuilderInstruction): TBuilderInstruction = {
      tla.filter(intName("t"), left, tla.bool(false))
    }

    val emptySet = dynEmpty(tla.enumSet(tla.int(1)))
    val pred = tla.gt(intName("x"), tla.int(4))
    val ex = tla.skolem(tla.exists(intName("x"), emptySet, pred))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)

    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // regression test, the buggy implementation failed here
    // E x \in {} is false
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(tla.unchecked(nextState.ex))))
  }

  test("""skolem: \E i \in Nat: i = 10 /\ x' \in {i}""") { rewriterType: SMTEncoding =>
    prepareArena()
    // this works for skolem constants only
    val ex =
      tla.skolem(
          tla.exists(intName("i"), tla.natSet(),
              tla.and(
                  tla.eql(intName("i"), tla.int(10)),
                  tla.assign(tla.prime(intName("x")), intName("i")),
              ))
      )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)

    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    val xp = nextState.binding("x'")
    val eql = tla.eql(cellEx(xp), tla.int(10))
    assertTlaExAndRestore(rewriter, nextState.setRex(eql))
  }

  test("""skolemization over range: \E i \in a..b: i % 3 = 1 /\ x' \in {i}""") { rewriterType: SMTEncoding =>
    // this works for skolem constants only
    prepareArena()
    val ex =
      tla.skolem(tla.exists(
              intName("i"),
              tla.dotdot(intName("a"), intName("b")),
              tla.and(
                  tla.eql(tla.mod(intName("i"), tla.int(3)), tla.int(1)),
                  tla.assign(tla.prime(intName("x")), intName("i")),
              ),
          ))

    val rewriter = create(rewriterType)

    // rewrite 5 and 9 first, to produce a and b
    var state = new SymbState(tla.int(5), arena, Binding())
    state = rewriter.rewriteUntilDone(state)
    val aCell = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(tla.int(9)))
    val bCell = state.asCell
    val binding: Binding = Binding("a" -> aCell, "b" -> bCell)

    val nextState = rewriter.rewriteUntilDone(state.setBinding(binding).setRex(ex))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    val xp = nextState.binding("x'")
    val eq = tla.eql(cellEx(xp), tla.int(7))
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""\A x \in {1, 2, 3}: x < 10 ~~> $B$k""") { rewriterType: SMTEncoding =>
    prepareArena()
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.forall(intName("x"), set123, tla.lt(intName("x"), tla.int(10)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assertUnsatOrExplain()
  }

  test("""\A x \in {1, 2, 3}: x > 2 ~~> $B$k""") { rewriterType: SMTEncoding =>
    prepareArena()
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3))
    val ex = tla.forall(intName("x"), set123, tla.gt(intName("x"), tla.int(2)))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create(rewriterType)
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain()
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(tla.unchecked(nextState.ex)))
    assert(solverContext.sat())
  }
}
