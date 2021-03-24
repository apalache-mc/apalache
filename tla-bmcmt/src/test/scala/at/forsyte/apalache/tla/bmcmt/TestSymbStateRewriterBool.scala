package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.NoRule
import at.forsyte.apalache.tla.bmcmt.types.{BoolT, FinSetT, IntT}
import at.forsyte.apalache.tla.lir.TypedPredefs._
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterBool extends RewriterBase with TestingPredefs with BeforeAndAfterEach {
  // these are handy variables that will be overwritten by before
  private var x: ArenaCell = new ArenaCell(100000, IntT())
  private var y: ArenaCell = new ArenaCell(100001, IntT())
  private var set: ArenaCell = new ArenaCell(100001, FinSetT(IntT()))
  private var xyBinding = Binding()
  private val boolTypes = Map("b" -> BoolT1(), "i" -> IntT1(), "I" -> SetT1(IntT1()))

  override def beforeEach() {
    super.beforeEach()

    arena = arena.appendCell(BoolT()) // we have to give bindings to the type finder
    x = arena.topCell
    arena = arena.appendCell(BoolT()) // we have to give bindings to the type finder
    y = arena.topCell
    arena = arena.appendCell(FinSetT(IntT()))
    set = arena.topCell
    xyBinding = Binding("x" -> x, "y" -> y, "S" -> set)
  }

  test("FALSE ~~> $C$0") {
    val ex = tla.bool(false).typed()
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$0")(Untyped())
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("TRUE ~~> $C$1") {
    val ex = tla.bool(true).typed()
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$1")(Untyped())
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("BOOLEAN ~~> c_BOOLEAN") {
    val boolset = tla.booleanSet().typed(SetT1(BoolT1()))
    val state = new SymbState(boolset, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$2")(Untyped())
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("x => y ~~> ~x \\/ y") {
    // outside of KerA+, should be handled by Keramelizer and Normalizer
    val ex = tla
      .impl(tla.name("x") ? "b", tla.name("y") ? "b")
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, xyBinding)
    assert(NoRule() == create().rewriteOnce(state))
  }

  test("x <=> y") {
    // outside of KerA+, should be handled by Keramelizer and Normalizer
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell
    val ex = tla
      .equiv(left.toNameEx ? "b", right.toNameEx ? "b")
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, xyBinding)
    assert(NoRule() == create().rewriteOnce(state))
  }

  test("""IF-THEN-ELSE with \E: IF \E i \in {}: x' \in {i} THEN x' ELSE 0""") {
    // this tricky test comes from Bakery, where an assignment is made in one branch of a conjunction
    val exists =
      tla
        .apalacheSkolem(tla.exists(tla.name("i") ? "i", tla.enumSet() ? "I",
                tla.in(tla.prime(tla.name("x") ? "i") ? "i", tla.enumSet(tla.name("i") ? "i") ? "I") ? "b") ? "b")
        .typed(boolTypes, "b")
    val ite = tla
      .ite(exists, tla.prime(tla.name("x") ? "i") ? "i", tla.int(0))
      .typed(boolTypes, "b")

    val state = new SymbState(ite, arena, Binding())
    val rewriter = new SymbStateRewriterImpl(solverContext)
    var nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    val eq = tla.eql(tla.int(0), nextState.ex).typed(BoolT1())
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""~c_i ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell

    val ex = tla.not(cell.toNameEx ? "b").typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            val eq = tla
              .eql(cell.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
              .typed(boolTypes, "b")
            solverContext.assertGroundExpr(eq)
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(tla.not(nextState.ex).typed(BoolT1()))
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~x ~~> TRUE""") {
    val ex = tla
      .not(tla.name("x") ? "b")
      .typed(boolTypes, "b")
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.eql(nextState.ex, tla.bool(true)).typed(BoolT1())))
  }

  test("""FALSE = TRUE ~~> FALSE""") {
    val ex = tla
      .eql(arena.cellFalse().toNameEx ? "b", arena.cellTrue().toNameEx ? "b")
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla
      .eql(nextState.ex, arena.cellFalse().toNameEx ? "b")
      .typed(boolTypes, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""x = TRUE ~~> FALSE when x = FALSE""") {
    val ex = tla
      .eql(tla.name("x") ? "b", tla.bool(true) ? "b")
      .typed(boolTypes, "b")
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla.eql(nextState.ex, tla.bool(false)).typed(BoolT1())
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""~(x = TRUE) ~~> TRUE when x = FALSE""") {
    val ex = tla
      .not(tla.eql(tla.name("x") ? "b", tla.bool(true)) ? "b")
      .typed(boolTypes, "b")
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    val eq = tla
      .eql(nextState.ex, tla.bool(true))
      .typed(boolTypes, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""FALSE /\ TRUE ~~> $B$0""") {
    val ex = tla
      .and(tla.bool(false), tla.bool(true))
      .typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(state.arena.cellFalse().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_1 /\ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val c1 = arena.topCell
    arena = arena.appendCell(BoolT())
    val c2 = arena.topCell

    val ex = tla
      .and(c1.toNameEx ? "b", c2.toNameEx ? "b")
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(solverContext.sat())
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            val eq1 = tla
              .eql(c1.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
              .typed(boolTypes, "b")
            solverContext.assertGroundExpr(eq1)
            assert(!solverContext.sat())
            rewriter.pop()
            val eq2 = tla
              .eql(c1.toNameEx ? "b", arena.cellTrue().toNameEx ? "")
              .typed(boolTypes, "b")
            solverContext.assertGroundExpr(eq2)
            assert(solverContext.sat())
            val eq3 = tla
              .eql(c2.toNameEx ? "b", arena.cellTrue().toNameEx ? "b")
              .typed(boolTypes, "b")
            solverContext.assertGroundExpr(eq3)
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""empty \/ ~~> $B$0""") {
    val ex = tla.or().typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellFalse().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""empty /\ ~~> $B$1""") {
    val ex = tla.and().typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellTrue().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""FALSE \/ TRUE ~~> $B$1""") {
    val ex = tla.or(tla.bool(false), tla.bool(true)).typed(BoolT1())
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellTrue().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""c_1 \/ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = tla
      .or(left.toNameEx ? "b", right.toNameEx ? "b")
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            val eq1 = tla
              .eql(left.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
              .typed(boolTypes, "b")
            solverContext.assertGroundExpr(eq1)
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            val eq2 = tla
              .eql(right.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
              .typed(boolTypes, "b")
            solverContext.assertGroundExpr(eq2)
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""~($B$1 = $B$2) ~~> $B$3""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = tla
      .not(tla.eql(left.toNameEx ? "b", right.toNameEx ? "b") ? "b")
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        solverContext.assertGroundExpr(predEx)
        rewriter.push()
        // both false
        assert(solverContext.sat())
        val eq1 = tla
          .eql(left.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
          .typed(boolTypes, "b")
        solverContext.assertGroundExpr(eq1)
        assert(solverContext.sat())
        rewriter.push()
        val eq2 = tla
          .eql(right.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
          .typed(boolTypes, "b")
        solverContext.assertGroundExpr(eq2)
        assert(!solverContext.sat())
        rewriter.pop()
        val eq3 = tla
          .eql(right.toNameEx ? "b", arena.cellTrue().toNameEx ? "b")
          .typed(boolTypes, "b")
        solverContext.assertGroundExpr(eq3)
        assert(solverContext.sat())
        rewriter.pop()
        // both true
        val eq4 = tla
          .eql(left.toNameEx ? "b", arena.cellTrue().toNameEx ? "b")
          .typed(boolTypes, "b")
        solverContext.assertGroundExpr(eq4)
        assert(solverContext.sat())
        rewriter.push()
        val eq5 = tla
          .eql(right.toNameEx ? "b", arena.cellTrue().toNameEx ? "b")
          .typed(boolTypes, "b")
        solverContext.assertGroundExpr(eq5)
        assert(!solverContext.sat())
        rewriter.pop()
        val eq6 = tla
          .eql(right.toNameEx ? "b", arena.cellFalse().toNameEx ? "b")
          .typed(boolTypes, "b")
        solverContext.assertGroundExpr(eq6)
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""\E x \in {}: TRUE ~~> FALSE""") {
    val ex = tla
      .exists(tla.name("x") ? "i", tla.enumSet() ? "I", tla.bool(true))
      .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    assert(arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""\E x \in {1, 2, 3}: x = 2 ~~> $B$k""") {
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3)).typed(SetT1(IntT1()))
    val ex =
      tla
        .exists(tla.name("x") ? "i", set123, tla.eql(tla.int(2), tla.name("x") ? "i") ? "b")
        .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex).typed(BoolT1()))
    assertUnsatOrExplain(rewriter, nextState)
  }

  /** Jure, 9.12.19: Why should this throw? */
  test("""\E x \in {1, 2}: y' := x ~~> 2 assignments, regression""") {
    val set12 = tla
      .enumSet(tla.int(1), tla.int(2))
      .typed(SetT1(IntT1()))
    // an assignment inside an existential quantifier is tricky, as we can multiple values to variables
    val ex = tla
      .exists(
          tla.name("x") ? "i",
          set12,
          tla.assign(tla.prime(tla.name("y") ? "i") ? "i", tla.name("x") ? "i") ? "b"
      )
      .typed(boolTypes, "b")
    ////
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    assertThrows[NotImplementedError] {
      // TODO: implement multiple assignments in expanded quantifiers
      val nextState = rewriter.rewriteUntilDone(state)
      assert(solverContext.sat())
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      assert(solverContext.sat())
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(tla.not(nextState.ex).typed(BoolT1()))
      assertUnsatOrExplain(rewriter, nextState)
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      val eq1 = tla
        .eql(tla.int(1), nextState.binding("y'").toNameEx ? "i")
        .typed(boolTypes, "b")
      solverContext.assertGroundExpr(eq1)
      assert(solverContext.sat())
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      val eq2 = tla
        .eql(tla.int(2), nextState.binding("y'").toNameEx ? "i")
        .typed(boolTypes, "b")
      solverContext.assertGroundExpr(eq2)
      assert(solverContext.sat())
      rewriter.pop()
    }
  }

  test("""\E x \in {1, 2, 3}: x > 4 ~~> $B$k""") {
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3)).typed(SetT1(IntT1()))
    val ex =
      tla
        .exists(tla.name("x") ? "i", set123, tla.gt(tla.name("x") ? "i", tla.int(4)) ? "b")
        .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex).typed(BoolT1()))
    assert(solverContext.sat())
  }

  test("""\E x \in {t \in {1}: FALSE}: x > 4, regression""") {
    def dynEmpty(left: TlaEx): TlaEx = {
      tla
        .filter(tla.name("t") ? "i", left ? "I", tla.bool(false))
        .typed(boolTypes, "I")
    }

    val emptySet = dynEmpty(tla.enumSet(tla.int(1)).typed(SetT1(IntT1())))
    val pred = tla.gt(tla.name("x") ? "i", tla.int(4)).typed(boolTypes, "b")
    val ex =
      tla
        .apalacheSkolem(tla.exists(tla.name("x") ? "i", emptySet, pred) ? "b")
        .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()

    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // regression test, the buggy implementation failed here
    // E x \in {} is false
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(nextState.ex).typed(BoolT1())))
  }

  test("""skolem: \E i \in Nat: i = 10 /\ x' \in {i}""") {
    // this works for skolem constants only
    val ex =
      tla
        .apalacheSkolem(tla.exists(tla.name("i") ? "i", tla.natSet() ? "I",
                tla.and(
                    tla.eql(tla.name("i") ? "i", tla.int(10)) ? "b",
                    tla.assign(tla.prime(tla.name("x") ? "i") ? "i", tla.name("i") ? "i") ? "b"
                ) ? "b") ? "b")
        .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()

    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    val xp = nextState.binding("x'")
    val eql = tla
      .eql(xp.toNameEx ? "i", tla.int(10))
      .typed(boolTypes, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eql))
  }

  test("""skolemization over range: \E i \in a..b: i % 3 = 1 /\ x' \in {i}""") {
    // this works for skolem constants only
    val ex =
      tla
        .apalacheSkolem(
            tla.exists(
                tla.name("i") ? "i",
                tla.dotdot(tla.name("a") ? "i", tla.name("b") ? "i") ? "I",
                tla.and(
                    tla.eql(tla.mod(tla.name("i") ? "i", tla.int(3)) ? "i", tla.int(1)) ? "b",
                    tla.assign(tla.prime(tla.name("x") ? "i") ? "i", tla.name("i") ? "i") ? "b"
                ) ? "b"
            ) ? "b")
        .typed(boolTypes, "b")

    val rewriter = create()

    // rewrite 5 and 9 first, to produce a and b
    var state = new SymbState(tla.int(5).typed(), arena, Binding())
    state = rewriter.rewriteUntilDone(state)
    val aCell = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(tla.int(9).typed()))
    val bCell = state.asCell
    val binding: Binding = Binding("a" -> aCell, "b" -> bCell)

    val nextState = rewriter.rewriteUntilDone(state.setBinding(binding).setRex(ex))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    val xp = nextState.binding("x'")
    val eq = tla
      .eql(xp.toNameEx ? "i", tla.int(7))
      .typed(boolTypes, "b")
    assertTlaExAndRestore(rewriter, nextState.setRex(eq))
  }

  test("""\A x \in {1, 2, 3}: x < 10 ~~> $B$k""") {
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3)).typed(SetT1(IntT1()))
    val ex =
      tla
        .forall(tla.name("x") ? "i", set123, tla.lt(tla.name("x") ? "i", tla.int(10)) ? "b")
        .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex).typed(BoolT1()))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""\A x \in {1, 2, 3}: x > 2 ~~> $B$k""") {
    val set123 = tla.enumSet(tla.int(1), tla.int(2), tla.int(3)).typed(SetT1(IntT1()))
    val ex =
      tla
        .forall(tla.name("x") ? "i", set123, tla.gt(tla.name("x") ? "i", tla.int(2)) ? "b")
        .typed(boolTypes, "b")
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex).typed(BoolT1()))
    assert(solverContext.sat())
  }
}
