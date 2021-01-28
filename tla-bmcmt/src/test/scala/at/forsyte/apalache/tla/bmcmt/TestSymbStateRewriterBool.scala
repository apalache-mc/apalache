package at.forsyte.apalache.tla.bmcmt

import at.forsyte.apalache.tla.bmcmt.SymbStateRewriter.NoRule
import at.forsyte.apalache.tla.bmcmt.smt.SolverContext
import at.forsyte.apalache.tla.bmcmt.types.eager.TrivialTypeFinder
import at.forsyte.apalache.tla.bmcmt.types.{
  AnnotationParser,
  BoolT,
  FinSetT,
  IntT
}
import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.lir.convenience.tla
import at.forsyte.apalache.tla.lir.oper.{BmcOper, TlaBoolOper, TlaOper}
import at.forsyte.apalache.tla.lir.values.{TlaBoolSet, TlaNatSet}
import at.forsyte.apalache.tla.lir.values.TlaBool
import org.junit.runner.RunWith
import org.scalatest.BeforeAndAfterEach
import org.scalatest.junit.JUnitRunner

import scala.collection.immutable.HashMap

@RunWith(classOf[JUnitRunner])
class TestSymbStateRewriterBool
    extends RewriterBase
    with TestingPredefs
    with BeforeAndAfterEach {
  // these are handy variables that will be overwritten by before
  private var x: ArenaCell = new ArenaCell(100000, IntT())
  private var y: ArenaCell = new ArenaCell(100001, IntT())
  private var set: ArenaCell = new ArenaCell(100001, FinSetT(IntT()))
  private var xyBinding = Binding()

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
    val ex = ValEx(TlaBool(false))
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$0")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("TRUE ~~> $C$1") {
    val ex = ValEx(TlaBool(true))
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$1")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-SET-BOOLEAN: BOOLEAN ~~> c_BOOLEAN") {
    val state = new SymbState(ValEx(TlaBoolSet), arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        val expected = NameEx("$C$2")
        assert(expected == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("SE-BOOL-IMPL: x => y ~~> ~x \\/ y") {
    // outside of KerA+, should be handled by Keramelizer and Normalizer
    val ex = tla.impl("x", "y")
    val state = new SymbState(ex, arena, xyBinding)
    assert(NoRule() == create().rewriteOnce(state))
  }

  test("SE-BOOL-EQUIV: x <=> y") {
    // outside of KerA+, should be handled by Keramelizer and Normalizer
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell
    val ex = tla.equiv(left.toNameEx, right.toNameEx)
    val state = new SymbState(ex, arena, xyBinding)
    assert(NoRule() == create().rewriteOnce(state))
  }

  test("""IF-THEN-ELSE with \E: IF \E i \in {}: x' \in {i} THEN x' ELSE 0""") {
    // this tricky test comes from Bakery, where an assignment is made in one branch of a conjunction
    val exists =
      OperEx(
        BmcOper.skolem,
        tla.exists(
          tla.name("i"),
          tla.withType(tla.enumSet(), AnnotationParser.toTla(FinSetT(IntT()))),
          tla.in(tla.prime(tla.name("x")), tla.enumSet(tla.name("i")))
        )
      )
    val ite = tla.ite(exists, tla.prime(tla.name("x")), tla.int(0))

    val state = new SymbState(ite, arena, Binding())
    val rewriter =
      new SymbStateRewriterImpl(solverContext, new TrivialTypeFinder())
    var nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(tla.int(0), nextState.ex))
    )
  }

  test("""SE-BOOL-NEG9: ~c_i ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val cell = arena.topCell

    val ex = OperEx(TlaBoolOper.not, cell.toNameEx)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            solverContext.assertGroundExpr(
              OperEx(TlaOper.eq, cell.toNameEx, arena.cellFalse().toNameEx)
            )
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(
              OperEx(TlaBoolOper.not, nextState.ex)
            )
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NEG9: ~x ~~> TRUE""") {
    val ex = OperEx(TlaBoolOper.not, NameEx("x"))
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(nextState.ex, tla.bool(true)))
    )
  }

  test("""FALSE = TRUE ~~> FALSE""") {
    val ex = tla.eql(arena.cellFalse().toNameEx, arena.cellTrue().toNameEx)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(nextState.ex, arena.cellFalse().toNameEx))
    )
  }

  test("""x = TRUE ~~> FALSE when x = FALSE""") {
    val ex = tla.eql(tla.name("x"), tla.bool(true))
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(nextState.ex, tla.bool(false)))
    )
  }

  test("""~(x = TRUE) ~~> TRUE when x = FALSE""") {
    val ex = tla.not(tla.eql(tla.name("x"), tla.bool(true)))
    val binding = Binding("x" -> arena.cellFalse())
    val state = new SymbState(ex, arena, binding)
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(nextState.ex, tla.bool(true)))
    )
  }

  test("""SE-AND1: FALSE /\ TRUE ~~> $B$0""") {
    val ex =
      OperEx(TlaBoolOper.and, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(state.arena.cellFalse().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: c_1 /\ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val c1 = arena.topCell
    arena = arena.appendCell(BoolT())
    val c2 = arena.topCell

    val ex = OperEx(TlaBoolOper.and, c1.toNameEx, c2.toNameEx)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            assert(solverContext.sat())
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            solverContext.assertGroundExpr(
              OperEx(TlaOper.eq, c1.toNameEx, arena.cellFalse().toNameEx)
            )
            assert(!solverContext.sat())
            rewriter.pop()
            solverContext.assertGroundExpr(
              OperEx(TlaOper.eq, c1.toNameEx, arena.cellTrue().toNameEx)
            )
            assert(solverContext.sat())
            solverContext.assertGroundExpr(
              OperEx(TlaOper.eq, c2.toNameEx, arena.cellTrue().toNameEx)
            )
            assert(solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR4: empty \/ ~~> $B$0""") {
    val ex = OperEx(TlaBoolOper.or)
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellFalse().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-AND4: empty /\ ~~> $B$1""") {
    val ex = OperEx(TlaBoolOper.and)
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellTrue().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR1: FALSE \/ TRUE ~~> $B$1""") {
    val ex = OperEx(TlaBoolOper.or, ValEx(TlaBool(false)), ValEx(TlaBool(true)))
    val state = new SymbState(ex, arena, Binding())
    create().rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        assert(arena.cellTrue().toNameEx == nextState.ex)
        assert(state.arena == nextState.arena)

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-OR5: c_1 \/ c_2 ~~> b_new""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = OperEx(TlaBoolOper.or, left.toNameEx, right.toNameEx)
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    rewriter.rewriteOnce(state) match {
      case SymbStateRewriter.Continue(nextState) =>
        nextState.ex match {
          case NameEx(name) =>
            solverContext.assertGroundExpr(
              OperEx(TlaOper.eq, left.toNameEx, arena.cellFalse().toNameEx)
            )
            solverContext.assertGroundExpr(nextState.ex)
            rewriter.push()
            assert(solverContext.sat())
            solverContext.assertGroundExpr(
              OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx)
            )
            assert(!solverContext.sat())

          case _ =>
            fail("Unexpected rewriting result")
        }

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-BOOL-NE1: ~($B$1 = $B$2) ~~> $B$3""") {
    arena = arena.appendCell(BoolT())
    val left = arena.topCell
    arena = arena.appendCell(BoolT())
    val right = arena.topCell

    val ex = tla.not(tla.eql(left.toNameEx, right.toNameEx))
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    nextState.ex match {
      case predEx @ NameEx(name) =>
        solverContext.assertGroundExpr(predEx)
        rewriter.push()
        // both false
        assert(solverContext.sat())
        solverContext.assertGroundExpr(
          OperEx(TlaOper.eq, left.toNameEx, arena.cellFalse().toNameEx)
        )
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(
          OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx)
        )
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(
          OperEx(TlaOper.eq, right.toNameEx, arena.cellTrue().toNameEx)
        )
        assert(solverContext.sat())
        rewriter.pop()
        // both true
        solverContext.assertGroundExpr(
          OperEx(TlaOper.eq, left.toNameEx, arena.cellTrue().toNameEx)
        )
        assert(solverContext.sat())
        rewriter.push()
        solverContext.assertGroundExpr(
          OperEx(TlaOper.eq, right.toNameEx, arena.cellTrue().toNameEx)
        )
        assert(!solverContext.sat())
        rewriter.pop()
        solverContext.assertGroundExpr(
          OperEx(TlaOper.eq, right.toNameEx, arena.cellFalse().toNameEx)
        )
        assert(solverContext.sat())

      case _ =>
        fail("Unexpected rewriting result")
    }
  }

  test("""SE-EX2: \E x \in {}: TRUE ~~> FALSE""") {
    val ex = tla.exists(tla.name("x"), tla.enumSet(), tla.bool(true))
    val state = new SymbState(ex, arena, Binding())
    val nextState = create().rewriteUntilDone(state)
    assert(arena.cellFalse().toNameEx == nextState.ex)
  }

  test("""SE-EX3: \E x \in {1, 2, 3}: x = 2 ~~> $B$k""") {
    val ex = tla.exists(
      tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.eql(tla.int(2), tla.name("x"))
    )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  /** Jure, 9.12.19: Why should this throw? */
  test("""SE-EX: \E x \in {1, 2}: y' = x ~~> 2 assignments, regression""") {
    // an assignment inside an existential quantifier is tricky, as we can multiple values to variables
    val ex = tla.exists(
      tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2)),
      tla.assignPrime(tla.name("y"), tla.name("x"))
    )
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
      solverContext.assertGroundExpr(tla.not(nextState.ex))
      assertUnsatOrExplain(rewriter, nextState)
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      solverContext.assertGroundExpr(
        tla.eql(tla.int(1), nextState.binding("y'").toNameEx)
      )
      assert(solverContext.sat())
      rewriter.pop()
      rewriter.push()
      solverContext.assertGroundExpr(nextState.ex)
      solverContext.assertGroundExpr(
        tla.eql(tla.int(2), nextState.binding("y'").toNameEx)
      )
      assert(solverContext.sat())
      rewriter.pop()
    }
  }

  test("""SE-EX3: \E x \in {1, 2, 3}: x > 4 ~~> $B$k""") {
    val ex = tla.exists(
      tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.gt(tla.name("x"), tla.int(4))
    )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(solverContext.sat())
  }

  test("""SE-EX: \E x \in {1} \ {1}: x > 4, regression""") {
    def dynEmpty(left: TlaEx): TlaEx = {
      tla.filter(tla.name("t"), left, tla.bool(false))
    }

    val ex =
      OperEx(
        BmcOper.skolem,
        tla.exists(
          tla.name("x"),
          dynEmpty(tla.enumSet(tla.int(1))),
          tla.gt(tla.name("x"), tla.int(4))
        )
      )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()

    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat()) // regression test, the buggy implementation failed here
    assertTlaExAndRestore(rewriter, nextState.setRex(tla.not(nextState.ex))) // E x \in {} is false
  }

  test("""SE-EX skolem: \E i \in Nat: i = 10 /\ x' \in {i}""") {
    // this works for skolem constants only
    val ex =
      OperEx(
        BmcOper.skolem,
        tla.exists(
          tla.name("i"),
          ValEx(TlaNatSet),
          tla.and(
            tla.eql(tla.name("i"), tla.int(10)),
            tla.assignPrime(tla.name("x"), tla.name("i"))
          )
        )
      )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()

    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    val xp = nextState.binding("x'")
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(xp.toNameEx, tla.int(10)))
    )
  }

  test(
    """SE-EX skolemization over range: \E i \in a..b: i % 3 = 1 /\ x' \in {i}"""
  ) {
    // this works for skolem constants only
    val ex =
      OperEx(
        BmcOper.skolem,
        tla.exists(
          tla.name("i"),
          tla.dotdot(tla.name("a"), tla.name("b")),
          tla.and(
            tla.eql(tla.mod(tla.name("i"), tla.int(3)), tla.int(1)),
            tla.assignPrime(tla.name("x"), tla.name("i"))
          )
        )
      ) ///

    val rewriter = create()

    // rewrite 5 and 9 first, to produce a and b
    var state = new SymbState(tla.int(5), arena, Binding())
    state = rewriter.rewriteUntilDone(state)
    val aCell = state.asCell
    state = rewriter.rewriteUntilDone(state.setRex(tla.int(9)))
    val bCell = state.asCell
    val binding: Binding = Binding("a" -> aCell, "b" -> bCell)

    val nextState =
      rewriter.rewriteUntilDone(state.setBinding(binding).setRex(ex))
    assert(solverContext.sat())
    solverContext.assertGroundExpr(nextState.ex)
    val xp = nextState.binding("x'")
    assertTlaExAndRestore(
      rewriter,
      nextState.setRex(tla.eql(xp.toNameEx, tla.int(7)))
    )
  }

  test("""SE-ALL3: \A x \in {1, 2, 3}: x < 10 ~~> $B$k""") {
    val ex = tla.forall(
      tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.lt(tla.name("x"), tla.int(10))
    )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assert(solverContext.sat())
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assertUnsatOrExplain(rewriter, nextState)
  }

  test("""SE-ALL3: \A x \in {1, 2, 3}: x > 2 ~~> $B$k""") {
    val ex = tla.forall(
      tla.name("x"),
      tla.enumSet(tla.int(1), tla.int(2), tla.int(3)),
      tla.gt(tla.name("x"), tla.int(2))
    )
    val state = new SymbState(ex, arena, Binding())
    val rewriter = create()
    val nextState = rewriter.rewriteUntilDone(state)
    assert(solverContext.sat())
    rewriter.push()
    solverContext.assertGroundExpr(nextState.ex)
    assertUnsatOrExplain(rewriter, nextState)
    rewriter.pop()
    solverContext.assertGroundExpr(tla.not(nextState.ex))
    assert(solverContext.sat())
  }
}
